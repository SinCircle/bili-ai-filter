// ==UserScript==
// @name         B站首页 AI/低质视频标记
// @namespace    https://github.com/SinCircle/bili-ai-filter
// @version      0.1.0
// @description  在B站首页识别低粉/新号/疑似AI视频；命中后整卡变淡，检测中右下角显示放大镜，不改原排版
// @author       SinCircle
// @match        https://www.bilibili.com/*
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_addStyle
// @grant        GM_registerMenuCommand
// @grant        unsafeWindow
// @connect      api.bilibili.com
// @run-at       document-start
// @noframes
// ==/UserScript==

(function () {
  'use strict';

  // ============================================================
  // 配置：改这里就能调阈值
  // ============================================================
  const CFG = {
    FANS_LOW: 10000,
    FANS_VERY_LOW: 1000,
    RECENT_WINDOW_DAYS: 7,
    RECENT_WEEK_MIN: 4,
    NEW_CREATOR_MS: 365 * 86400000,
    FLAG_SCORE: 60,
    CONTENT_MIN: 10,
    UP_TTL: 24 * 3600000,
    VIEW_TTL: 24 * 3600000,
    AGE_TTL: 7 * 86400000,
    AGE_FAIL_TTL: 3600000,
    WBI_TTL: 6 * 3600000,
    CACHE_MAX: 2000,
    AGE_PAGE_SIZE: 50,
    QUEUE_CONCURRENCY: 2,
    QUEUE_GAP_MS: 450,
    QUEUE_JITTER_MS: 250,
    BACKOFF_MS: 60000,
  };

  const STORE_UP = 'baf_up_cache_v1';
  const STORE_VIEW = 'baf_view_cache_v1';
  const STORE_AGE = 'baf_age_cache_v1';
  const STORE_ENABLED = 'baf_enabled_v1';

  // ============================================================
  // 小工具
  // ============================================================
  function sleep(ms) {
    return new Promise((resolve) => setTimeout(resolve, ms));
  }

  function parseDuration(text) {
    const parts = String(text || '').trim().split(':').map(Number);
    if (!parts.length || parts.some(Number.isNaN)) return 0;
    return parts.reduce((acc, value) => acc * 60 + value, 0);
  }

  function parseCount(text) {
    const match = String(text || '').trim().match(/([\d.]+)\s*([万亿]?)/);
    if (!match) return 0;
    const unit = match[2] === '万' ? 1e4 : match[2] === '亿' ? 1e8 : 1;
    return Math.round(parseFloat(match[1]) * unit);
  }

  function formatCount(value) {
    const n = Number(value) || 0;
    const trim = (x) => (Math.round(x * 10) / 10).toString();
    if (n >= 1e8) return `${trim(n / 1e8)}亿`;
    if (n >= 1e4) return `${trim(n / 1e4)}万`;
    return String(Math.round(n));
  }

  function normalizeTitle(title) {
    return String(title || '')
      .replace(/[\s\p{P}\p{S}]/gu, '')
      .toLowerCase();
  }

  const TEMPLATE_WORDS = [
    '教程', '保姆级', '零基础', '全流程', '2026', '吊打付费', '一键', '速成',
    '合集', '超详细', '手把手', '从零开始', '玩转', '天花板', '什么',
  ];
  const TOOL_WORDS = [
    'AIGC', 'Sora', '可灵', '即梦', 'ComfyUI', 'MiniMax', 'Seedance',
    '豆包', 'Runway', 'Pika', 'Luma', '海螺', 'Vidu', '剪映',
  ];
  const COURSE_WORDS = [
    'AIGC', 'AI教程', 'AI课程', 'AI漫剧', 'AI短剧', 'AI视频', '人工智能',
    '变现', '副业', '引流', '加微信', '训练营', '陪跑', '免费领取', '资料领取',
  ];
  const STRONG_COURSE_WORDS = new Set([
    'AIGC', 'AI教程', 'AI课程', 'AI漫剧', 'AI短剧', 'AI视频', '人工智能', 'AI',
  ]);

  function matchTitleSignals(title) {
    const text = String(title || '');
    const lower = text.toLowerCase();
    const hits = [];
    for (const word of TOOL_WORDS) {
      if (lower.includes(word.toLowerCase())) hits.push(word);
    }
    if (/(?<![A-Za-z])AI(?![A-Za-z])/.test(text)) hits.push('AI');
    for (const word of TEMPLATE_WORDS) {
      if (text.includes(word)) hits.push(word);
    }
    if (/全\d+集/.test(text)) hits.push('全N集');
    return [...new Set(hits)];
  }

  function matchCourseSignals(text) {
    const source = String(text || '');
    const lower = source.toLowerCase();
    const hits = [];
    for (const word of COURSE_WORDS) {
      if (lower.includes(word.toLowerCase())) hits.push(word);
    }
    if (/(?<![A-Za-z])AI(?![A-Za-z])/.test(source)) hits.push('AI');
    return [...new Set(hits)];
  }

  const AI_ARGUE_RE = /(AI生成|含\s*AI|人工智能|AI技术|AI合成|合成技术|生成合成)/i;

  function isAiArgue(message) {
    return AI_ARGUE_RE.test(String(message || ''));
  }

  function isFresh(entry, ttl, now = Date.now()) {
    return Boolean(entry && entry.ts && now - entry.ts < ttl);
  }

  function itemCreated(item) {
    return Number(item && (item.created ?? item.pubdate ?? item.ctime)) || 0;
  }

  function countRecentVideos(vlist, nowSeconds = Math.floor(Date.now() / 1000)) {
    const windowStart = nowSeconds - CFG.RECENT_WINDOW_DAYS * 86400;
    return (vlist || []).filter((item) => itemCreated(item) >= windowStart).length;
  }

  // ============================================================
  // MD5（wbi 签名用；标准 RFC 1321 实现）
  // ============================================================
  function md5(input) {
    const bytes = new TextEncoder().encode(String(input));
    const length = bytes.length;
    const bitLength = length * 8;
    const paddedLength = (((length + 8) >> 6) + 1) * 64;
    const buffer = new Uint8Array(paddedLength);
    buffer.set(bytes);
    buffer[length] = 0x80;
    const view = new DataView(buffer.buffer);
    view.setUint32(paddedLength - 8, bitLength >>> 0, true);
    view.setUint32(paddedLength - 4, Math.floor(bitLength / 0x100000000), true);

    const shifts = [7, 12, 17, 22, 5, 9, 14, 20, 4, 11, 16, 23, 6, 10, 15, 21];
    const K = new Uint32Array(64);
    for (let i = 0; i < 64; i += 1) {
      K[i] = Math.floor(Math.abs(Math.sin(i + 1)) * 0x100000000) >>> 0;
    }

    let a0 = 0x67452301;
    let b0 = 0xefcdab89;
    let c0 = 0x98badcfe;
    let d0 = 0x10325476;

    for (let offset = 0; offset < paddedLength; offset += 64) {
      const words = new Uint32Array(16);
      for (let i = 0; i < 16; i += 1) {
        words[i] = view.getUint32(offset + i * 4, true);
      }
      let A = a0;
      let B = b0;
      let C = c0;
      let D = d0;
      for (let i = 0; i < 64; i += 1) {
        let F;
        let g;
        if (i < 16) {
          F = (B & C) | (~B & D);
          g = i;
        } else if (i < 32) {
          F = (D & B) | (~D & C);
          g = (5 * i + 1) % 16;
        } else if (i < 48) {
          F = B ^ C ^ D;
          g = (3 * i + 5) % 16;
        } else {
          F = C ^ (B | ~D);
          g = (7 * i) % 16;
        }
        const previousD = D;
        D = C;
        C = B;
        const sum = (A + F + K[i] + words[g]) >>> 0;
        const shift = shifts[(i >> 4) * 4 + (i % 4)];
        B = (B + ((sum << shift) | (sum >>> (32 - shift)))) >>> 0;
        A = previousD;
      }
      a0 = (a0 + A) >>> 0;
      b0 = (b0 + B) >>> 0;
      c0 = (c0 + C) >>> 0;
      d0 = (d0 + D) >>> 0;
    }

    const out = new Uint8Array(16);
    const outView = new DataView(out.buffer);
    outView.setUint32(0, a0, true);
    outView.setUint32(4, b0, true);
    outView.setUint32(8, c0, true);
    outView.setUint32(12, d0, true);
    return [...out].map((byte) => byte.toString(16).padStart(2, '0')).join('');
  }

  // ============================================================
  // wbi 签名
  // ============================================================
  const MIXIN_TAB = [
    46, 47, 18, 2, 53, 8, 23, 32, 15, 50, 10, 31, 58, 3, 45, 35,
    27, 43, 5, 49, 33, 9, 42, 19, 29, 28, 14, 39, 12, 38, 41, 13,
    37, 48, 7, 16, 24, 55, 40, 61, 26, 17, 0, 1, 60, 51, 30, 4,
    22, 25, 54, 21, 56, 59, 6, 63, 57, 62, 11, 36, 20, 34, 44, 52,
  ];

  function mixinKeyFromUrls(imgUrl, subUrl) {
    const base = (url) => String(url || '').split('/').pop().split('.')[0];
    const raw = base(imgUrl) + base(subUrl);
    return MIXIN_TAB.map((index) => raw[index]).join('').slice(0, 32);
  }

  function signWbi(params, mixinKey, wts = Math.floor(Date.now() / 1000)) {
    const all = { ...params, wts };
    const query = Object.keys(all)
      .sort()
      .map((key) => {
        const value = String(all[key]).replace(/[!'()*]/g, '');
        return `${encodeURIComponent(key)}=${encodeURIComponent(value)}`;
      })
      .join('&');
    return `${query}&w_rid=${md5(query + mixinKey)}`;
  }

  // ============================================================
  // 存储与缓存
  // ============================================================
  const storage = (() => {
    if (typeof GM_getValue === 'function' && typeof GM_setValue === 'function') {
      return {
        get: (key, fallback) => GM_getValue(key, fallback),
        set: (key, value) => GM_setValue(key, value),
      };
    }
    const memory = new Map();
    return {
      get: (key, fallback) => (memory.has(key) ? memory.get(key) : fallback),
      set: (key, value) => memory.set(key, value),
    };
  })();

  function loadStore(key) {
    try {
      const raw = storage.get(key, '{}');
      const parsed = typeof raw === 'string' ? JSON.parse(raw) : raw;
      return parsed && typeof parsed === 'object' ? parsed : {};
    } catch {
      return {};
    }
  }

  function pruneStore(object, max = CFG.CACHE_MAX) {
    const keys = Object.keys(object);
    if (keys.length <= max) return object;
    keys.sort((a, b) => (object[a].ts || 0) - (object[b].ts || 0));
    for (let i = 0; i < keys.length - max; i += 1) delete object[keys[i]];
    return object;
  }

  const upCache = pruneStore(loadStore(STORE_UP));
  const viewCache = pruneStore(loadStore(STORE_VIEW));
  const ageCache = pruneStore(loadStore(STORE_AGE));

  let saveTimer = 0;
  const dirty = { up: false, view: false, age: false };

  function flushCaches() {
    if (saveTimer) {
      clearTimeout(saveTimer);
      saveTimer = 0;
    }
    try {
      if (dirty.up) {
        storage.set(STORE_UP, JSON.stringify(upCache));
        dirty.up = false;
      }
      if (dirty.view) {
        storage.set(STORE_VIEW, JSON.stringify(viewCache));
        dirty.view = false;
      }
      if (dirty.age) {
        storage.set(STORE_AGE, JSON.stringify(ageCache));
        dirty.age = false;
      }
    } catch (error) {
      console.warn('[BAF] 缓存写入失败', error);
    }
  }

  function scheduleSave(kind) {
    if (kind) dirty[kind] = true;
    if (saveTimer) return;
    saveTimer = setTimeout(flushCaches, 1200);
  }

  if (typeof window !== 'undefined' && window.addEventListener) {
    window.addEventListener('pagehide', flushCaches);
  }

  // ============================================================
  // 请求队列
  // ============================================================
  class TaskQueue {
    constructor(options = {}) {
      this.concurrency = options.concurrency ?? CFG.QUEUE_CONCURRENCY;
      this.minGap = options.minGap ?? CFG.QUEUE_GAP_MS;
      this.jitter = options.jitter ?? CFG.QUEUE_JITTER_MS;
      this.backoffMs = options.backoffMs ?? CFG.BACKOFF_MS;
      this.active = 0;
      this.nextAt = 0;
      this.pauseUntil = 0;
      this.inflight = new Map();
    }

    push(key, task) {
      if (this.inflight.has(key)) return this.inflight.get(key);
      const promise = this.run(task).finally(() => this.inflight.delete(key));
      this.inflight.set(key, promise);
      return promise;
    }

    async run(task) {
      while (this.active >= this.concurrency) await sleep(40);
      this.active += 1;
      try {
        const pause = this.pauseUntil - Date.now();
        if (pause > 0) await sleep(pause);
        const wait = this.nextAt - Date.now();
        if (wait > 0) await sleep(wait);
        this.nextAt = Date.now() + this.minGap + Math.random() * this.jitter;
        return await task();
      } finally {
        this.active -= 1;
      }
    }

    backoff(ms = this.backoffMs) {
      this.pauseUntil = Math.max(this.pauseUntil, Date.now() + ms);
    }
  }

  const apiQueue = new TaskQueue();
  const ageQueue = new TaskQueue({ concurrency: 1, minGap: 1000, jitter: 300 });

  // ============================================================
  // 页面内 fetch（必须带 Cookie；api.bilibili.com 只认 bilibili.com 的 Origin）
  // ============================================================
  const pageFetch = (() => {
    try {
      if (typeof unsafeWindow !== 'undefined' && unsafeWindow.fetch) {
        return unsafeWindow.fetch.bind(unsafeWindow);
      }
    } catch {
      // ignore
    }
    if (typeof fetch === 'function') return fetch.bind(globalThis);
    return null;
  })();

  async function apiGet(url, queue = apiQueue) {
    if (!pageFetch) throw new Error('fetch 不可用');
    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), 15000);
    let response;
    try {
      response = await pageFetch(url, { credentials: 'include', signal: controller.signal });
    } finally {
      clearTimeout(timer);
    }
    if (response.status === 412 || response.status === 429) {
      queue.backoff();
      throw new Error(`HTTP ${response.status}`);
    }
    const json = await response.json();
    if (json.code === -799 || json.code === -352) {
      queue.backoff();
      const error = new Error(`B站风控 ${json.code}`);
      error.code = json.code;
      throw error;
    }
    if (json.code !== 0) {
      const error = new Error(json.message || `code ${json.code}`);
      error.code = json.code;
      throw error;
    }
    return json.data;
  }

  // ============================================================
  // 接口加载
  // ============================================================
  const upLoading = new Map();
  const viewLoading = new Map();
  const ageLoading = new Map();

  function mapCardData(data) {
    const card = data && data.card;
    if (!card) return null;
    const verify = card.official_verify || {};
    return {
      fans: Number(card.fans) || 0,
      archive: Number(data.archive_count) || 0,
      name: card.name || '',
      sign: card.sign || '',
      level: card.level_info ? Number(card.level_info.current_level) || 0 : 0,
      verified: Number(verify.type) >= 0 && Boolean(String(verify.desc || '').trim()),
      ts: Date.now(),
    };
  }

  function mapViewData(data) {
    if (!data) return null;
    const stat = data.stat || {};
    return {
      argueMsg: data.argue_info ? data.argue_info.argue_msg || '' : '',
      pubdate: Number(data.pubdate) || 0,
      duration: Number(data.duration) || 0,
      tname: data.tname || '',
      stat: {
        view: Number(stat.view) || 0,
        like: Number(stat.like) || 0,
        coin: Number(stat.coin) || 0,
      },
      ts: Date.now(),
    };
  }

  async function loadUp(mid) {
    if (!mid) return null;
    const cached = upCache[mid];
    if (isFresh(cached, CFG.UP_TTL)) return cached;
    if (upLoading.has(mid)) return upLoading.get(mid);
    const promise = apiQueue
      .push(`up:${mid}`, async () => {
        const data = await apiGet(
          `https://api.bilibili.com/x/web-interface/card?mid=${encodeURIComponent(mid)}`,
        );
        const entry = mapCardData(data);
        if (!entry) throw new Error('card 为空');
        upCache[mid] = entry;
        scheduleSave('up');
        return entry;
      })
      .catch(() => cached || null)
      .finally(() => upLoading.delete(mid));
    upLoading.set(mid, promise);
    return promise;
  }

  async function loadView(bvid) {
    if (!bvid) return null;
    const cached = viewCache[bvid];
    if (isFresh(cached, CFG.VIEW_TTL)) return cached;
    if (viewLoading.has(bvid)) return viewLoading.get(bvid);
    const promise = apiQueue
      .push(`view:${bvid}`, async () => {
        const data = await apiGet(
          `https://api.bilibili.com/x/web-interface/view?bvid=${encodeURIComponent(bvid)}`,
        );
        const entry = mapViewData(data);
        if (!entry) throw new Error('view 为空');
        viewCache[bvid] = entry;
        scheduleSave('view');
        return entry;
      })
      .catch(() => cached || null)
      .finally(() => viewLoading.delete(bvid));
    viewLoading.set(bvid, promise);
    return promise;
  }

  let wbiKey = '';
  let wbiKeyAt = 0;
  let wbiPromise = null;

  async function getWbiKey() {
    if (wbiKey && Date.now() - wbiKeyAt < CFG.WBI_TTL) return wbiKey;
    if (wbiPromise) return wbiPromise;
    wbiPromise = (async () => {
      if (!pageFetch) return '';
      const response = await pageFetch('https://api.bilibili.com/x/web-interface/nav', {
        credentials: 'include',
      });
      const json = await response.json();
      const image = json && json.data && json.data.wbi_img;
      if (!image) return '';
      wbiKey = mixinKeyFromUrls(image.img_url, image.sub_url);
      wbiKeyAt = Date.now();
      return wbiKey;
    })()
      .catch(() => '')
      .finally(() => {
        wbiPromise = null;
      });
    return wbiPromise;
  }

  async function fetchArcPage(mid, page, mixinKey) {
    const params = {
      mid,
      pn: page,
      ps: CFG.AGE_PAGE_SIZE,
      order: 'pubdate',
      platform: 'web',
      web_location: 1550101,
      order_avoided: true,
    };
    const query = signWbi(params, mixinKey);
    return apiGet(`https://api.bilibili.com/x/space/wbi/arc/search?${query}`, ageQueue);
  }

  async function loadAge(mid) {
    if (!mid) return null;
    const cached = ageCache[mid];
    if (cached) {
      if (cached.failed && isFresh(cached, CFG.AGE_FAIL_TTL)) return cached;
      if (!cached.failed && isFresh(cached, CFG.AGE_TTL)) return cached;
    }
    if (ageLoading.has(mid)) return ageLoading.get(mid);
    const promise = ageQueue
      .push(`age:${mid}`, async () => {
        const key = await getWbiKey();
        if (!key) throw new Error('wbi key 为空');
        const first = await fetchArcPage(mid, 1, key);
        const total = Number(first && first.page && first.page.count) || 0;
        const firstList = (first && first.list && first.list.vlist) || [];
        if (!total || !firstList.length) {
          return { failed: true, ts: Date.now() };
        }
        const nowSeconds = Math.floor(Date.now() / 1000);
        const recentCount = countRecentVideos(firstList, nowSeconds);
        let oldest = Math.min(
          ...firstList.map((item) => itemCreated(item) || Number.MAX_SAFE_INTEGER),
        );
        let oldestKnown = true;
        if (total > firstList.length) {
          const pageSize = firstList.length || CFG.AGE_PAGE_SIZE;
          const pages = Math.ceil(total / pageSize);
          if (pages > 1) {
            await sleep(800);
            try {
              const last = await fetchArcPage(mid, pages, key);
              const lastList = (last && last.list && last.list.vlist) || [];
              oldest = Math.min(
                oldest,
                ...lastList.map((item) => itemCreated(item) || Number.MAX_SAFE_INTEGER),
              );
            } catch {
              // 最早投稿拿不到时保留最近 7 天投稿数
              oldestKnown = false;
            }
          }
        }
        const entry =
          oldestKnown && Number.isFinite(oldest) && oldest !== Number.MAX_SAFE_INTEGER
            ? { firstPubdate: oldest, recentCount, ts: Date.now() }
            : { firstPubdate: 0, recentCount, ts: Date.now() };
        ageCache[mid] = entry;
        scheduleSave('age');
        return entry;
      })
      .catch(() => {
        const entry = { failed: true, ts: Date.now() };
        ageCache[mid] = entry;
        scheduleSave('age');
        return entry;
      })
      .finally(() => ageLoading.delete(mid));
    ageLoading.set(mid, promise);
    return promise;
  }

  // ============================================================
  // 页面卡片解析
  // ============================================================
  function findCover(card) {
    const direct = card.querySelector('.bili-video-card__image, .bili-cover-card__image');
    if (direct) return direct;
    const picture = card.querySelector('.bili-video-card__cover, .cover');
    if (picture && picture.tagName === 'PICTURE') return picture.parentElement || picture;
    return picture;
  }

  function extractCard(card) {
    const owner = card.querySelector('a[href*="space.bilibili.com/"]');
    const mid = owner
      ? (String(owner.getAttribute('href') || '').match(/space\.bilibili\.com\/(\d+)/) || [])[1] || ''
      : '';
    const videoLink = card.querySelector('a[href*="/video/"]');
    const bvid = videoLink
      ? (String(videoLink.getAttribute('href') || '').match(/\/video\/(BV[0-9A-Za-z]+)/) || [])[1] || ''
      : '';
    const titleElement = card.querySelector('.bili-video-card__info--tit, h3[title]');
    const title = String(
      (titleElement && (titleElement.getAttribute('title') || titleElement.textContent)) || '',
    ).trim();
    const authorElement = card.querySelector('.bili-video-card__info--author');
    const upName = String(
      (authorElement && (authorElement.getAttribute('title') || authorElement.textContent)) || '',
    ).trim();
    const durationElement = card.querySelector('.bili-video-card__stats__duration');
    const duration = parseDuration(durationElement ? durationElement.textContent : '');
    const playElement = card.querySelector('.bili-video-card__stats--text');
    const play = parseCount(playElement ? playElement.textContent : '');
    const cover = findCover(card);
    return { mid, bvid, title, upName, duration, play, cover };
  }

  // ============================================================
  // 评分
  // ============================================================
  function scoreCard(state, now = Date.now()) {
    const info = state.info || {};
    const up = state.up;
    const view = state.view;
    const age = state.age;
    let score = 0;
    let content = 0;
    let strongContent = 0;
    const reasons = [];
    let lowFans = false;
    let recentHeavy = false;
    let newCreator = false;
    let officialAI = false;
    let recentCount = 0;

    const add = (points, reason, isContent = false, isStrong = false) => {
      score += points;
      if (isContent) content += points;
      if (isStrong) strongContent += points;
      reasons.push(reason);
    };

    if (up) {
      const fans = Number(up.fans) || 0;
      if (fans < CFG.FANS_LOW) {
        lowFans = true;
        add(25, `粉丝 ${fans.toLocaleString()} < 1万`);
      }
      if (fans < CFG.FANS_VERY_LOW) add(15, `粉丝 ${fans.toLocaleString()} < 1000`);
      if (!up.verified) add(5, '无官方认证');
      const courseHits = matchCourseSignals(`${up.name || ''} ${up.sign || ''}`);
      const strongCourse = courseHits.filter((word) => STRONG_COURSE_WORDS.has(word));
      const weakCourse = courseHits.filter((word) => !STRONG_COURSE_WORDS.has(word));
      if (strongCourse.length) {
        add(15, `名称/简介含 AI 课程词：${strongCourse.join('、')}`, true, true);
      }
      if (weakCourse.length) {
        add(5, `名称/简介含营销词：${weakCourse.join('、')}`);
      }
    }

    const titleHits = matchTitleSignals(info.title);
    const titleToolHits = titleHits.filter(
      (word) => word === 'AI' || TOOL_WORDS.includes(word),
    );
    const titleTemplateHits = titleHits.filter((word) => !titleToolHits.includes(word));
    if (titleToolHits.length) {
      add(
        Math.min(20, titleToolHits.length * 10),
        `标题含工具名：${titleToolHits.join('、')}`,
        true,
        true,
      );
    }
    if (titleTemplateHits.length) {
      add(
        Math.min(10, titleTemplateHits.length * 5),
        `标题模板词：${titleTemplateHits.join('、')}`,
        true,
      );
    }

    const duration = Number(info.duration) || Number(view && view.duration) || 0;
    if (duration > 7200) {
      add(10, `时长 ${Math.round(duration / 60)} 分钟 > 2 小时`, true);
    } else if (duration > 0 && duration < 60) {
      add(10, `时长 ${duration} 秒 < 1 分钟`, true);
    }

    if (state.matrix) add(30, '同标题矩阵号（≥3 个不同 UP）', true, true);

    if (view) {
      if (isAiArgue(view.argueMsg)) {
        officialAI = true;
        add(100, `官方 AI 声明：${view.argueMsg}`, true, true);
      }
      const stat = view.stat || {};
      const views = Number(stat.view) || 0;
      const likes = Number(stat.like) || 0;
      const coins = Number(stat.coin) || 0;
      if (views >= 1000) {
        const likeRate = likes / views;
        const coinRate = likes > 0 ? coins / likes : 0;
        if (likeRate < 0.01) {
          add(15, `赞播比 ${(likeRate * 100).toFixed(2)}% < 1%`, true, true);
        } else if (likeRate > 0.3 && coinRate < 0.05) {
          add(
            20,
            `赞播比 ${(likeRate * 100).toFixed(0)}%，币赞比 ${coinRate.toFixed(2)} < 0.05`,
            true,
            true,
          );
        }
      }
    }

    if (age) {
      if (age.firstPubdate) {
        const ageDays = Math.floor((now - age.firstPubdate * 1000) / 86400000);
        if (ageDays >= 0 && ageDays < 365) {
          newCreator = true;
          add(20, `最早投稿 ${ageDays} 天前 < 1 年`);
        }
      }
      recentCount = Number(age.recentCount) || 0;
      if (recentCount >= CFG.RECENT_WEEK_MIN) {
        recentHeavy = true;
        add(20, `最近 7 天投稿 ${recentCount} 个 ≥ 4`, true, true);
      }
    }

    const flagged = score >= CFG.FLAG_SCORE && strongContent >= CFG.CONTENT_MIN;
    const tags = [];
    if (flagged) tags.push({ text: '疑似AI', cls: 'flag' });
    if (officialAI) tags.push({ text: 'AI声明', cls: 'official' });
    if (lowFans) tags.push({ text: `粉${formatCount(up.fans)}`, cls: 'fact' });
    if (recentHeavy) tags.push({ text: `7天${recentCount}稿`, cls: 'fact' });
    if (newCreator) tags.push({ text: '创作<1年', cls: 'fact' });

    return { score, content, strongContent, flagged, officialAI, reasons, tags, titleHits };
  }

  // ============================================================
  // 角标注入
  // ============================================================
  const CSS = `
.baf-loading{position:absolute;right:2px;bottom:2px;z-index:4;display:inline-flex;align-items:center;justify-content:center;width:18px;height:18px;color:#61666d;pointer-events:none;filter:drop-shadow(0 0 2px rgba(255,255,255,.9));}
.baf-loading svg{width:12px;height:12px;display:block;animation:baf-search 1.2s ease-in-out infinite;transform-origin:55% 45%;}
@keyframes baf-search{0%,100%{transform:scale(1) rotate(-8deg);opacity:.55}50%{transform:scale(1.18) rotate(8deg);opacity:1}}
@media (prefers-reduced-motion: reduce){.baf-loading svg{animation:none;}}
.bili-video-card.baf-dim{opacity:.3;transition:opacity .15s ease;}
.bili-video-card.baf-dim:hover{opacity:1;}
body.baf-off .bili-video-card.baf-dim{opacity:1!important;}
body.baf-off .baf-loading{display:none!important;}
`;

  function updateLoadingIcon(card, show) {
    let icon = card.querySelector('.baf-loading');
    if (!show) {
      if (icon) icon.remove();
      return;
    }
    if (icon) return;
    icon = createLoadingIcon();
    card.appendChild(icon);
    try {
      if (typeof getComputedStyle === 'function') {
        const position = getComputedStyle(card).position;
        if (!position || position === 'static') card.style.position = 'relative';
      }
    } catch {
      // ignore
    }
  }

  function renderState(card, state, options = {}) {
    const now = options.now || Date.now();
    const result = scoreCard(state, now);
    state.lastResult = result;
    const detecting = Boolean(state.detecting);
    card.classList.toggle('baf-dim', result.flagged && !detecting);
    updateLoadingIcon(card, detecting);
    return result;
  }

  function createLoadingIcon() {
    const element = document.createElement('span');
    element.className = 'baf-loading';
    element.title = '检测中…';
    element.innerHTML =
      '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" aria-hidden="true"><circle cx="10.5" cy="10.5" r="6.5"></circle><path d="M15.5 15.5 21 21"></path></svg>';
    return element;
  }

  // ============================================================
  // 同标题矩阵检测
  // ============================================================
  class TitleMatrix {
    constructor(threshold = 3, minLength = 8) {
      this.threshold = threshold;
      this.minLength = minLength;
      this.groups = new Map();
    }

    add(title, mid) {
      const key = normalizeTitle(title);
      if (!key || key.length < this.minLength) {
        return { key, count: 0, triggered: false };
      }
      let group = this.groups.get(key);
      if (!group) {
        group = { mids: new Set(), triggered: false };
        this.groups.set(key, group);
        if (this.groups.size > 500) {
          const oldest = this.groups.keys().next().value;
          this.groups.delete(oldest);
        }
      }
      const before = group.mids.size;
      group.mids.add(String(mid));
      const triggered = !group.triggered && before < this.threshold && group.mids.size >= this.threshold;
      if (triggered) group.triggered = true;
      return { key, count: group.mids.size, triggered };
    }
  }

  // ============================================================
  // 状态与调度
  // ============================================================
  const states = new Map();
  const midCards = new Map();
  const matrix = new TitleMatrix();

  function markMatrix(key) {
    const group = matrix.groups.get(key);
    if (!group) return;
    for (const mid of group.mids) {
      const cards = midCards.get(mid);
      if (!cards) continue;
      for (const card of cards) {
        const state = states.get(card);
        if (state && normalizeTitle(state.info.title) === key) {
          state.matrix = true;
          renderState(card, state);
        }
      }
    }
  }

  async function maybeLoadAge(card, state) {
    if (!state.up || state.up.fans >= CFG.FANS_LOW) return;
    // 总投稿还不够 4 个时，不可能在最近 7 天发 4 个，省掉请求
    if ((Number(state.up.archive) || 0) < CFG.RECENT_WEEK_MIN) return;
    if (state.ageLoading || state.ageDone) return;

    state.ageLoading = true;
    const entry = await loadAge(state.info.mid);
    state.ageLoading = false;
    state.ageDone = true;
    if (states.get(card) !== state || !card.isConnected) return;
    if (entry && !entry.failed) {
      state.age = entry;
      renderState(card, state);
    }
  }

  async function hydrate(card, state) {
    if (state.hydrating) return;
    state.hydrating = true;
    try {
      const up = await loadUp(state.info.mid);
      if (states.get(card) !== state || !card.isConnected) return;
      if (up) {
        state.up = up;
        renderState(card, state);
      }
      if (up && up.fans < CFG.FANS_LOW && state.info.bvid) {
        const view = await loadView(state.info.bvid);
        if (states.get(card) !== state || !card.isConnected) return;
        if (view) {
          state.view = view;
          renderState(card, state);
        }
        await maybeLoadAge(card, state);
      }
    } finally {
      state.hydrating = false;
      state.detecting = false;
      if (states.get(card) === state && card.isConnected) renderState(card, state);
    }
  }

  function enrichCard(card) {
    if (!card || card.nodeType !== 1) return;
    const info = extractCard(card);
    if (!info.mid || !info.bvid) return;

    const key = `${info.mid}|${info.bvid}`;
    if (card.dataset.bafKey === key && states.has(card)) {
      const existing = states.get(card);
      const needsWork =
        existing.detecting ||
        (existing.lastResult && existing.lastResult.flagged);
      if (needsWork) renderState(card, existing);
      return;
    }

    const previous = states.get(card);
    if (previous && previous.info && previous.info.mid !== info.mid) {
      const previousSet = midCards.get(previous.info.mid);
      if (previousSet) previousSet.delete(card);
    }

    card.dataset.bafKey = key;
    const state = {
      info,
      up: null,
      view: null,
      age: null,
      matrix: false,
      hydrating: false,
      detecting: true,
      ageLoading: false,
      ageDone: false,
      lastResult: null,
    };
    states.set(card, state);

    let cards = midCards.get(info.mid);
    if (!cards) {
      cards = new Set();
      midCards.set(info.mid, cards);
    }
    cards.add(card);

    const matrixHit = matrix.add(info.title, info.mid);
    if (matrixHit.triggered) {
      markMatrix(matrixHit.key);
    }
    const group = matrix.groups.get(matrixHit.key);
    if (group && group.triggered) state.matrix = true;

    renderState(card, state);
    hydrate(card, state);
  }

  const CARD_SELECTOR = '.bili-video-card';

  function scanAll(root = document) {
    if (!root || typeof root.querySelectorAll !== 'function') return;
    root.querySelectorAll(CARD_SELECTOR).forEach(enrichCard);
  }

  const pendingCards = new Set();
  let rafId = 0;
  const scheduleFrame =
    typeof requestAnimationFrame === 'function'
      ? requestAnimationFrame
      : (callback) => setTimeout(callback, 16);

  const observer = new MutationObserver((records) => {
    for (const record of records) {
      for (const node of record.addedNodes) {
        if (node.nodeType !== 1) continue;
        if (node.matches && node.matches(CARD_SELECTOR)) pendingCards.add(node);
        if (node.querySelectorAll) {
          node.querySelectorAll(CARD_SELECTOR).forEach((element) => pendingCards.add(element));
        }
        if (node.closest) {
          const ownerCard = node.closest(CARD_SELECTOR);
          if (ownerCard) pendingCards.add(ownerCard);
        }
      }
    }
    if (!pendingCards.size || rafId) return;
    rafId = scheduleFrame(() => {
      rafId = 0;
      const batch = [...pendingCards];
      pendingCards.clear();
      batch.forEach(enrichCard);
    });
  });

  // ============================================================
  // 启动
  // ============================================================
  function isHomePage() {
    return (
      location.hostname === 'www.bilibili.com' &&
      (location.pathname === '/' || location.pathname === '/index.html')
    );
  }

  function injectCSS() {
    if (typeof GM_addStyle === 'function') {
      GM_addStyle(CSS);
      return;
    }
    const style = document.createElement('style');
    style.textContent = CSS;
    document.head.appendChild(style);
  }

  function applyEnabled(enabled) {
    if (document.body) document.body.classList.toggle('baf-off', !enabled);
  }

  function registerMenu() {
    if (typeof GM_registerMenuCommand !== 'function') return;
    GM_registerMenuCommand('暂停/恢复标记', () => {
      const next = !Boolean(storage.get(STORE_ENABLED, true));
      storage.set(STORE_ENABLED, next);
      applyEnabled(next);
    });
    GM_registerMenuCommand('清除 UP/视频缓存', () => {
      if (!confirm('清除缓存并刷新页面？')) return;
      storage.set(STORE_UP, '{}');
      storage.set(STORE_VIEW, '{}');
      storage.set(STORE_AGE, '{}');
      location.reload();
    });
    GM_registerMenuCommand('重新扫描当前页面', () => scanAll(document));
  }

  function start() {
    injectCSS();
    applyEnabled(Boolean(storage.get(STORE_ENABLED, true)));
    scanAll(document);
    if (document.body) {
      observer.observe(document.body, { childList: true, subtree: true });
    }
    registerMenu();
    setInterval(() => {
      for (const [card, state] of states) {
        if (!card.isConnected) {
          states.delete(card);
          const cards = midCards.get(state.info.mid);
          if (cards) cards.delete(card);
          continue;
        }
        const needsWork =
          state.detecting ||
          (state.lastResult && state.lastResult.flagged);
        if (needsWork) renderState(card, state);
      }
    }, 3000);
  }

  function boot() {
    if (!isHomePage()) return;
    if (document.body) {
      start();
    } else {
      document.addEventListener('DOMContentLoaded', start, { once: true });
    }
  }

  // ============================================================
  // 导出（Node 验收脚本用；浏览器里走 boot）
  // ============================================================
  const CORE = {
    CFG,
    parseDuration,
    parseCount,
    formatCount,
    normalizeTitle,
    matchTitleSignals,
    matchCourseSignals,
    isAiArgue,
    isFresh,
    countRecentVideos,
    md5,
    mixinKeyFromUrls,
    signWbi,
    TaskQueue,
    TitleMatrix,
    extractCard,
    scoreCard,
    renderState,
    mapCardData,
    mapViewData,
  };

  const isNode =
    typeof module !== 'undefined' &&
    module.exports &&
    typeof process !== 'undefined' &&
    process.versions &&
    process.versions.node;

  if (isNode) {
    module.exports = CORE;
  } else {
    boot();
  }
})();
