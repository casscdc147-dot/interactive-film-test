/**
 * 《美妆女王》互动影游网页版 v4 — 核心播放与交互状态机引擎
 *
 * 核心工程保障：
 * 1. 首屏绝对静音（Mode.MENU）：sessionActive=false 期间所有 <video> 强制 muted=true、volume=0、preload 按需受控，
 *    且挂载硬件级 play 事件守卫，在用户点击「开始游戏 / 继续」前绝不产生任何音频输出。
 * 2. 第一段 1.0x 原速流畅播放：全生命周期锁定 defaultPlaybackRate=1.0 与 playbackRate=1.0（含 ratechange 瞬时回正），
 *    首屏静默预缓冲 01-1.mp4，开播前 1.2 秒独占解码与带宽，随后再错峰顺序预加载 02a / 02b。
 * 3. 零黑屏无缝切镜：三槽 <video> 循环复用（优先分配已获用户手势授权的 blessed 槽位）+ 720×1280 末帧 Canvas 冻结桥接。
 */
(function () {
  'use strict';

  const SAVE_KEY = 'beauty_queen_web_v4_save';
  const META_KEY = 'beauty_queen_web_v4_meta';

  const Mode = Object.freeze({
    MENU: 'MENU',
    LOADING: 'LOADING',
    PLAYING: 'PLAYING',
    CHOICES: 'CHOICES',
    ENDING: 'ENDING',
    ERROR: 'ERROR'
  });

  // DOM 引用
  const dom = {
    stage: document.getElementById('stage'),
    freezeCanvas: document.getElementById('freeze-canvas'),
    stageScrim: document.getElementById('stage-scrim'),
    videoEls: [
      document.getElementById('video-slot-0'),
      document.getElementById('video-slot-1'),
      document.getElementById('video-slot-2')
    ],
    coverLayer: document.getElementById('cover-layer'),
    coverStatusPill: document.getElementById('cover-status-pill'),
    coverStatusDot: document.getElementById('cover-status-dot'),
    coverStatusText: document.getElementById('cover-status-text'),
    btnStartHotspot: document.getElementById('btn-start-hotspot'),
    btnContinueGame: document.getElementById('btn-continue-game'),

    hudTop: document.getElementById('hud-top'),
    clipProgressFill: document.getElementById('clip-progress-fill'),
    btnNodeIndicator: document.getElementById('btn-node-indicator'),
    hudNodeLabel: document.getElementById('hud-node-label'),
    btnToggleMute: document.getElementById('btn-toggle-mute'),
    iconSoundOn: document.getElementById('icon-sound-on'),
    iconSoundOff: document.getElementById('icon-sound-off'),
    btnOpenTree: document.getElementById('btn-open-tree'),
    btnPause: document.getElementById('btn-pause'),
    btnUnlockAudio: document.getElementById('btn-unlock-audio'),

    loadingOverlay: document.getElementById('loading-overlay'),
    loadingText: document.getElementById('loading-text'),

    choiceLayer: document.getElementById('choice-layer'),
    choiceStepBadge: document.getElementById('choice-step-badge'),
    btnChoicePrev: document.getElementById('btn-choice-prev'),
    btnChoiceReplay: document.getElementById('btn-choice-replay'),
    choicePrompt: document.getElementById('choice-prompt'),
    countdownFill: document.getElementById('countdown-fill'),
    countdownSeconds: document.getElementById('countdown-seconds'),
    btnOptionA: document.getElementById('btn-option-a'),
    btnOptionB: document.getElementById('btn-option-b'),
    optionATitle: document.getElementById('option-a-title'),
    optionASub: document.getElementById('option-a-sub'),
    optionBTitle: document.getElementById('option-b-title'),
    optionBSub: document.getElementById('option-b-sub'),

    endingLayer: document.getElementById('ending-layer'),
    endingAchievement: document.getElementById('ending-achievement'),
    endingTitle: document.getElementById('ending-title'),
    endingSubtitle: document.getElementById('ending-subtitle'),
    endingCollectionStat: document.getElementById('ending-collection-stat'),
    endingRouteChips: document.getElementById('ending-route-chips'),
    btnEndingBack: document.getElementById('btn-ending-back'),
    btnEndingRestart: document.getElementById('btn-ending-restart'),
    btnEndingHome: document.getElementById('btn-ending-home'),

    pauseModal: document.getElementById('pause-modal'),
    btnClosePause: document.getElementById('btn-close-pause'),
    volumeSlider: document.getElementById('volume-slider'),
    volumeValue: document.getElementById('volume-value'),
    btnResume: document.getElementById('btn-resume'),
    btnReplayCurrent: document.getElementById('btn-replay-current'),
    btnPauseBack: document.getElementById('btn-pause-back'),
    btnPauseTree: document.getElementById('btn-pause-tree'),
    btnFullscreen: document.getElementById('btn-fullscreen'),
    btnPauseHome: document.getElementById('btn-pause-home'),

    treeModal: document.getElementById('tree-modal'),
    treeProgressSummary: document.getElementById('tree-progress-summary'),
    storyGraph: document.getElementById('story-graph'),
    btnCloseTree: document.getElementById('btn-close-tree'),

    errorModal: document.getElementById('error-modal'),
    errorMessage: document.getElementById('error-message'),
    btnErrorRetry: document.getElementById('btn-error-retry'),
    btnErrorHome: document.getElementById('btn-error-home')
  };

  const freezeCtx = dom.freezeCanvas.getContext('2d', { alpha: false });

  // 三槽视频池状态封装
  const slots = dom.videoEls.map((el, index) => ({
    index,
    el,
    nodeId: null,
    src: '',
    blessed: false
  }));

  const state = {
    story: null,
    nodeMap: new Map(),
    mode: Mode.MENU,
    sessionActive: false, // false 时全局硬静音守卫生效，严禁任何音视频出声
    opToken: 0,
    activeSlotIndex: -1,
    preloadScheduledForNode: null,

    currentNodeId: '01',
    history: [], // [{ node: '01', option: 0|1, target: '02a'|'02b' }]

    paused: false,
    treeOpen: false,
    audioBlockedByPolicy: false,

    volume: 1.0,
    userMuted: false,

    choiceDuration: 5.0,
    choiceRemaining: 5.0,
    choiceLocked: false,
    choiceRafId: 0,
    choiceLastTs: 0,

    loadingTimerId: 0,

    visitedNodes: new Set(),
    completedRoutes: new Set()
  };

  /* ==========================================================================
     速率锁与首屏静音硬守卫
     ========================================================================== */

  function enforceNormalRate(el) {
    if (!el) return;
    if (el.defaultPlaybackRate !== 1.0) el.defaultPlaybackRate = 1.0;
    if (el.playbackRate !== 1.0) el.playbackRate = 1.0;
  }

  function applyAudioStateToElement(el, isActivePlayingSlot) {
    if (!el) return;
    if (!state.sessionActive || !isActivePlayingSlot) {
      el.muted = true;
      el.volume = 0;
      return;
    }
    const effectiveMuted = state.userMuted || state.audioBlockedByPolicy || state.volume <= 0;
    el.muted = effectiveMuted;
    el.volume = effectiveMuted ? 0 : Math.max(0, Math.min(1, state.volume));
  }

  function syncAllAudioStates() {
    slots.forEach((slot, idx) => {
      const isPlayingActive =
        state.sessionActive &&
        idx === state.activeSlotIndex &&
        (state.mode === Mode.PLAYING || state.mode === Mode.LOADING);
      applyAudioStateToElement(slot.el, isPlayingActive);
    });
    dom.iconSoundOn.classList.toggle('hidden', state.userMuted || state.volume <= 0);
    dom.iconSoundOff.classList.toggle('hidden', !(state.userMuted || state.volume <= 0));
    dom.volumeSlider.value = String(Math.round((state.userMuted ? 0 : state.volume) * 100));
    dom.volumeValue.textContent = `${Math.round((state.userMuted ? 0 : state.volume) * 100)}%`;
    dom.btnUnlockAudio.classList.toggle('hidden', !state.audioBlockedByPolicy);
  }

  function initVideoSlots() {
    slots.forEach((slot) => {
      const el = slot.el;
      el.muted = true;
      el.volume = 0;
      el.autoplay = false;
      el.loop = false;
      enforceNormalRate(el);

      // 硬性要求 2 守卫：未点击开始前任何意外触发的 play 立即静音并暂停
      el.addEventListener('play', () => {
        enforceNormalRate(el);
        if (!state.sessionActive) {
          el.muted = true;
          el.volume = 0;
          el.pause();
        }
      });

      // 硬性要求 1 守卫：全生命周期锁定 1.0 倍速
      ['loadedmetadata', 'loadeddata', 'canplay', 'playing', 'ratechange'].forEach((evt) => {
        el.addEventListener(evt, () => enforceNormalRate(el));
      });

      el.addEventListener('timeupdate', () => {
        if (slot.index !== state.activeSlotIndex || state.mode !== Mode.PLAYING) return;
        updatePlaybackProgress(el);
        maybeTriggerStaggeredPreload(el);
      });

      el.addEventListener('ended', () => {
        if (slot.index !== state.activeSlotIndex || state.mode !== Mode.PLAYING) return;
        onActiveClipEnded(slot);
      });

      el.addEventListener('error', () => {
        if (slot.index !== state.activeSlotIndex || !state.sessionActive) return;
        const code = el.error ? el.error.code : 0;
        showError(`视频片段加载失败（节点 ${state.currentNodeId}，错误码 ${code}）。\n请检查网络连接后点击重试。`);
      });
    });
  }

  /* ==========================================================================
     本地存储（进度存档、音量偏好、探索收集度）
     ========================================================================== */

  function loadMetaPreferences() {
    try {
      const raw = localStorage.getItem(META_KEY);
      if (!raw) return;
      const parsed = JSON.parse(raw);
      if (typeof parsed.volume === 'number' && parsed.volume >= 0 && parsed.volume <= 1) {
        state.volume = parsed.volume;
      }
      if (typeof parsed.userMuted === 'boolean') {
        state.userMuted = parsed.userMuted;
      }
      if (Array.isArray(parsed.visitedNodes)) {
        parsed.visitedNodes.forEach((id) => state.visitedNodes.add(id));
      }
      if (Array.isArray(parsed.completedRoutes)) {
        parsed.completedRoutes.forEach((r) => state.completedRoutes.add(r));
      }
    } catch (_e) {
      // 忽略隐私模式存储限制
    }
  }

  function saveMetaPreferences() {
    try {
      localStorage.setItem(
        META_KEY,
        JSON.stringify({
          volume: state.volume,
          userMuted: state.userMuted,
          visitedNodes: Array.from(state.visitedNodes),
          completedRoutes: Array.from(state.completedRoutes)
        })
      );
    } catch (_e) {
      // 忽略隐私模式存储限制
    }
  }

  function isReachableSequentially(fromId, targetId) {
    const visited = new Set();
    let cur = fromId;
    while (cur && !visited.has(cur)) {
      visited.add(cur);
      if (cur === targetId) return true;
      const node = state.nodeMap.get(cur);
      if (!node || node.ending || !node.next) return false;
      cur = node.next;
    }
    return false;
  }

  function readValidSave() {
    try {
      const raw = localStorage.getItem(SAVE_KEY);
      if (!raw || !state.story) return null;
      const data = JSON.parse(raw);
      if (
        !data ||
        data.schemaVersion !== 1 ||
        data.storyRevision !== state.story.revision ||
        !Array.isArray(data.history) ||
        !state.nodeMap.has(data.currentNode)
      ) {
        return null;
      }
      let expected = state.story.startNode;
      for (const rec of data.history) {
        if (!rec || (rec.option !== 0 && rec.option !== 1)) return null;
        if (!isReachableSequentially(expected, rec.node)) return null;
        const choiceNode = state.nodeMap.get(rec.node);
        if (!choiceNode || choiceNode.ending || choiceNode.next) return null;
        const expectedTarget = rec.option === 0 ? choiceNode.targetA : choiceNode.targetB;
        if (rec.target !== expectedTarget) return null;
        expected = rec.target;
      }
      if (!isReachableSequentially(expected, data.currentNode)) return null;
      return data;
    } catch (_e) {
      return null;
    }
  }

  function persistSessionSave() {
    if (!state.story) return;
    try {
      localStorage.setItem(
        SAVE_KEY,
        JSON.stringify({
          schemaVersion: 1,
          storyRevision: state.story.revision,
          currentNode: state.currentNodeId,
          history: state.history
        })
      );
    } catch (_e) {
      // 忽略无痕模式配额异常
    }
    refreshCoverContinueButton();
  }

  function refreshCoverContinueButton() {
    const saved = readValidSave();
    // 若存档已在起始节点 01 且无历史选择，无需重复显示“继续”按钮
    if (!saved || (saved.currentNode === state.story.startNode && saved.history.length === 0)) {
      dom.btnContinueGame.classList.add('hidden');
      return;
    }
    const savedNode = state.nodeMap.get(saved.currentNode);
    const shortTitle = savedNode ? savedNode.title : saved.currentNode;
    dom.btnContinueGame.textContent = `继续上次进度（${shortTitle}）`;
    dom.btnContinueGame.classList.remove('hidden');
  }

  /* ==========================================================================
     画布末帧冻结与三槽智能调度预加载
     ========================================================================== */

  function captureFreezeFrame(videoEl) {
    if (!videoEl || videoEl.readyState < 2 || !videoEl.videoWidth || !videoEl.videoHeight) {
      return false;
    }
    try {
      if (
        dom.freezeCanvas.width !== videoEl.videoWidth ||
        dom.freezeCanvas.height !== videoEl.videoHeight
      ) {
        dom.freezeCanvas.width = videoEl.videoWidth;
        dom.freezeCanvas.height = videoEl.videoHeight;
      }
      freezeCtx.drawImage(videoEl, 0, 0, dom.freezeCanvas.width, dom.freezeCanvas.height);
      dom.freezeCanvas.classList.add('is-visible');
      return true;
    } catch (_e) {
      return false;
    }
  }

  function clearFreezeCanvas() {
    dom.freezeCanvas.classList.remove('is-visible');
  }

  function assignSlotSource(slot, node) {
    if (!slot || !node) return;
    if (slot.nodeId === node.id && slot.src === node.video) {
      return;
    }
    const el = slot.el;
    el.pause();
    el.muted = true;
    el.volume = 0;
    slot.nodeId = node.id;
    slot.src = node.video;
    el.preload = 'auto';
    el.src = node.video;
    enforceNormalRate(el);
    el.load();
  }

  /**
   * 为即将到来的分支或顺播节点分配空闲预加载槽位。
   * 优先选择已经过用户点击手势解锁（blessed === true）的空闲槽位承载顺播 next 与超时默认项 targetA，
   * 确保在 iOS Safari 上自动汇回主线或倒计时超时跳转时也能直接带声音无缝起播。
   */
  function pickStandbySlot(excludeIndices, preferBlessed) {
    const candidates = slots.filter((s) => !excludeIndices.has(s.index));
    if (candidates.length === 0) return null;
    if (preferBlessed) {
      const blessedSlot = candidates.find((s) => s.blessed);
      if (blessedSlot) return blessedSlot;
    }
    return candidates[0];
  }

  function maybeTriggerStaggeredPreload(activeEl) {
    const node = state.nodeMap.get(state.currentNodeId);
    if (!node || node.ending) return;
    if (state.preloadScheduledForNode === node.id) return;

    // 第一段 01-1.mp4 至少稳定播放 1.2 秒后再启动后台分支预加载，杜绝首段解码与带宽争抢
    const minLeadSec = node.id === state.story.startNode ? 1.2 : 0.35;
    if (activeEl.currentTime < minLeadSec) return;

    state.preloadScheduledForNode = node.id;
    const used = new Set([state.activeSlotIndex]);

    if (node.next) {
      const nextNode = state.nodeMap.get(node.next);
      if (!nextNode) return;
      const existing = slots.find((s) => !used.has(s.index) && s.nodeId === nextNode.id);
      const slot = existing || pickStandbySlot(used, true);
      if (slot) assignSlotSource(slot, nextNode);
      return;
    }

    // 选择节点：先预加载默认分支 A，待 A 就绪（或 1.2 秒后）再顺序预加载分支 B
    const nodeA = state.nodeMap.get(node.targetA);
    const nodeB = state.nodeMap.get(node.targetB);
    if (!nodeA || !nodeB) return;

    let slotA = slots.find((s) => !used.has(s.index) && s.nodeId === nodeA.id);
    if (!slotA) slotA = pickStandbySlot(used, true);
    if (slotA) {
      used.add(slotA.index);
      assignSlotSource(slotA, nodeA);
    }

    let slotB = slots.find((s) => !used.has(s.index) && s.nodeId === nodeB.id);
    if (!slotB) slotB = pickStandbySlot(used, false);
    if (slotB) {
      const triggerB = () => {
        if (state.currentNodeId === node.id && slotB.index !== state.activeSlotIndex) {
          assignSlotSource(slotB, nodeB);
        }
      };
      if (slotA && slotA.el.readyState >= 3) {
        triggerB();
      } else if (slotA) {
        let fired = false;
        const once = () => {
          if (fired) return;
          fired = true;
          slotA.el.removeEventListener('canplay', once);
          triggerB();
        };
        slotA.el.addEventListener('canplay', once);
        setTimeout(once, 1400);
      } else {
        triggerB();
      }
    }
  }

  /* ==========================================================================
     核心播放跳转与末帧回溯定位
     ========================================================================== */

  function showDeferredLoading(label) {
    clearTimeout(state.loadingTimerId);
    dom.loadingText.textContent = label || '正在加载片段…';
    state.loadingTimerId = window.setTimeout(() => {
      if (state.mode === Mode.LOADING) {
        dom.loadingOverlay.classList.remove('hidden');
      }
    }, 180);
  }

  function hideDeferredLoading() {
    clearTimeout(state.loadingTimerId);
    dom.loadingOverlay.classList.add('hidden');
  }

  function waitForMediaReady(el, minReadyState, timeoutMs) {
    if (el.readyState >= minReadyState) return Promise.resolve();
    return new Promise((resolve, reject) => {
      let settled = false;
      const timer = setTimeout(() => {
        cleanup();
        if (el.readyState >= 2) resolve();
        else reject(new Error('视频缓冲超时，请检查网络连接。'));
      }, timeoutMs);

      const onReady = () => {
        if (el.readyState >= minReadyState) {
          cleanup();
          resolve();
        }
      };
      const onError = () => {
        cleanup();
        reject(new Error('视频文件读取失败。'));
      };
      function cleanup() {
        if (settled) return;
        settled = true;
        clearTimeout(timer);
        el.removeEventListener('loadedmetadata', onReady);
        el.removeEventListener('loadeddata', onReady);
        el.removeEventListener('canplay', onReady);
        el.removeEventListener('error', onError);
      }

      el.addEventListener('loadedmetadata', onReady);
      el.addEventListener('loadeddata', onReady);
      el.addEventListener('canplay', onReady);
      el.addEventListener('error', onError);
    });
  }

  function seekToTime(el, targetTime, timeoutMs) {
    return new Promise((resolve) => {
      let done = false;
      const finish = () => {
        if (done) return;
        done = true;
        clearTimeout(timer);
        el.removeEventListener('seeked', finish);
        resolve();
      };
      const timer = setTimeout(finish, timeoutMs);
      el.addEventListener('seeked', finish);
      try {
        el.currentTime = targetTime;
      } catch (_e) {
        finish();
      }
    });
  }

  function activateSlotVisual(slotIndex) {
    state.activeSlotIndex = slotIndex;
    slots.forEach((s, idx) => {
      s.el.classList.toggle('is-active', idx === slotIndex);
    });
  }

  function updateHudForNode(node) {
    dom.hudNodeLabel.textContent = node.title || node.id;
    dom.clipProgressFill.style.width = '0%';
  }

  function updatePlaybackProgress(el) {
    const dur = el.duration || (state.nodeMap.get(state.currentNodeId)?.duration ?? 0);
    if (dur > 0) {
      const pct = Math.max(0, Math.min(100, (el.currentTime / dur) * 100));
      dom.clipProgressFill.style.width = `${pct.toFixed(1)}%`;
    }
  }

  /**
   * 播放或定位到指定剧情节点。
   * @param {string} nodeId 目标节点 ID
   * @param {object} options { restoreChoice: 仅解码末帧并直接弹出选项, fromUserGesture: 是否处于用户点击调用栈内 }
   */
  async function playNode(nodeId, options = {}) {
    const { restoreChoice = false, fromUserGesture = false } = options;
    const node = state.nodeMap.get(nodeId);
    if (!node) {
      showError(`未找到剧情节点：${nodeId}`);
      return;
    }

    const opId = ++state.opToken;
    stopChoiceClock();
    state.paused = false;
    state.preloadScheduledForNode = null;
    state.currentNodeId = node.id;
    state.visitedNodes.add(node.id);
    saveMetaPreferences();
    persistSessionSave();

    // 切镜前将上一活跃视频当前帧冻结在底层画布上，彻底消除任何黑屏闪烁
    const prevSlot = slots[state.activeSlotIndex] || null;
    if (prevSlot) {
      captureFreezeFrame(prevSlot.el);
      prevSlot.el.pause();
      applyAudioStateToElement(prevSlot.el, false);
    }

    // 切换 UI 层隐显
    dom.coverLayer.classList.add('hidden');
    dom.hudTop.classList.remove('hidden');
    dom.choiceLayer.classList.add('hidden');
    dom.endingLayer.classList.add('hidden');
    dom.pauseModal.classList.add('hidden');
    dom.errorModal.classList.add('hidden');
    dom.stageScrim.classList.remove('is-dimmed');
    updateHudForNode(node);

    // 选择目标播放槽：优先命中已预加载该节点的槽位；否则挑选空闲槽（非手势触发时优先挑已 blessed 槽）
    let targetSlot = slots.find((s) => s.nodeId === node.id);
    if (!targetSlot) {
      const exclude = new Set(prevSlot ? [prevSlot.index] : []);
      targetSlot = pickStandbySlot(exclude, !fromUserGesture) || slots[0];
      assignSlotSource(targetSlot, node);
    }

    const el = targetSlot.el;
    enforceNormalRate(el);

    // 分支回溯模式：直接定位到选择节点视频末帧并打开抉择界面
    if (restoreChoice) {
      state.mode = Mode.LOADING;
      showDeferredLoading('正在回溯至选择点…');
      try {
        applyAudioStateToElement(el, false);
        await waitForMediaReady(el, 1, 15000);
        if (opId !== state.opToken) return;

        const targetSec = Math.max(0, (el.duration || node.duration || 1) - 0.08);
        await seekToTime(el, targetSec, 3000);
        await waitForMediaReady(el, 2, 8000);
        if (opId !== state.opToken) return;

        el.pause();
        activateSlotVisual(targetSlot.index);
        captureFreezeFrame(el);
        dom.clipProgressFill.style.width = '100%';
        hideDeferredLoading();
        enterChoicesMode(node);
        // 顺便后台预加载该选择节点的 A/B 分支
        state.preloadScheduledForNode = null;
        maybeTriggerStaggeredPreload({ currentTime: 999 });
      } catch (err) {
        if (opId !== state.opToken) return;
        hideDeferredLoading();
        showError(err.message || '回溯定位失败，请重试。');
      }
      return;
    }

    // 正常播放模式：重置时间轴至 0 并以 1.0x 原速起播
    state.mode = Mode.LOADING;
    try {
      if (el.readyState >= 1 && el.currentTime > 0.05) {
        el.currentTime = 0;
      }
    } catch (_e) {
      // metadata 尚未到达时无需重置
    }

    applyAudioStateToElement(el, true);
    enforceNormalRate(el);

    // 若处于用户手势内且缓冲已达 HAVE_CURRENT_DATA，同步调用 play() 立即解锁移动端音轨权限
    let syncPlayPromise = null;
    if (fromUserGesture && el.readyState >= 2) {
      syncPlayPromise = el.play();
    } else if (fromUserGesture) {
      // 即使缓冲尚未完成，也在手势栈内同步发起 play() 以锁定 iOS WebKit 音频授权
      syncPlayPromise = el.play();
      showDeferredLoading('正在准备视频…');
    } else if (el.readyState < 3) {
      showDeferredLoading('正在加载下一幕…');
    }

    try {
      if (syncPlayPromise) {
        await syncPlayPromise;
        targetSlot.blessed = true;
        state.audioBlockedByPolicy = false;
      } else {
        await waitForMediaReady(el, 3, 20000);
        if (opId !== state.opToken) return;
        enforceNormalRate(el);
        applyAudioStateToElement(el, true);
        await el.play();
        targetSlot.blessed = true;
        state.audioBlockedByPolicy = false;
      }
    } catch (playErr) {
      if (opId !== state.opToken) return;
      const isNotAllowed =
        playErr && (playErr.name === 'NotAllowedError' || /gesture|interact/i.test(playErr.message));

      if (!isNotAllowed) {
        hideDeferredLoading();
        showError(`无法播放片段 ${node.id}：${playErr ? playErr.message : '未知媒体错误'}`);
        return;
      }

      // 自动跳转在严格 WebKit 下若因目标槽未单独授权被拒，优先借用已 blessed 的槽位无缝接管
      const blessedFallback = slots.find((s) => s.blessed && s.index !== targetSlot.index);
      let recoveredWithAudio = false;
      if (blessedFallback && !state.userMuted) {
        try {
          assignSlotSource(blessedFallback, node);
          await waitForMediaReady(blessedFallback.el, 3, 12000);
          if (opId !== state.opToken) return;
          enforceNormalRate(blessedFallback.el);
          applyAudioStateToElement(blessedFallback.el, true);
          await blessedFallback.el.play();
          targetSlot = blessedFallback;
          recoveredWithAudio = true;
          state.audioBlockedByPolicy = false;
        } catch (_fallbackErr) {
          recoveredWithAudio = false;
        }
      }

      // 终极兜底：若浏览器仍拦截有声自动播放，先静音流畅播放并弹出顶部一键恢复原声横幅，绝不卡死剧情
      if (!recoveredWithAudio) {
        try {
          state.audioBlockedByPolicy = true;
          targetSlot.el.muted = true;
          targetSlot.el.volume = 0;
          enforceNormalRate(targetSlot.el);
          await waitForMediaReady(targetSlot.el, 2, 15000);
          if (opId !== state.opToken) return;
          await targetSlot.el.play();
        } catch (fatalErr) {
          hideDeferredLoading();
          showError(`浏览器阻止了视频播放，请点击重试。\n(${fatalErr ? fatalErr.message : ''})`);
          return;
        }
      }
    }

    if (opId !== state.opToken) return;
    enforceNormalRate(targetSlot.el);
    activateSlotVisual(targetSlot.index);
    state.mode = Mode.PLAYING;
    syncAllAudioStates();
    hideDeferredLoading();

    // 待新视频首帧稳定上屏后撤下底层冻结画布，避免后续切镜残留旧帧
    requestAnimationFrame(() => {
      if (opId === state.opToken && state.mode === Mode.PLAYING) {
        clearFreezeCanvas();
      }
    });
  }

  /* ==========================================================================
     片段结束流转：顺播汇回主线 / 弹出 5 秒分支抉择 / 结局成就结算
     ========================================================================== */

  function onActiveClipEnded(slot) {
    const node = state.nodeMap.get(state.currentNodeId);
    if (!node) return;

    slot.el.pause();
    captureFreezeFrame(slot.el);
    dom.clipProgressFill.style.width = '100%';

    if (node.ending) {
      enterEndingMode(node);
      return;
    }

    if (node.next) {
      playNode(node.next, { restoreChoice: false, fromUserGesture: false });
      return;
    }

    enterChoicesMode(node);
  }

  function enterChoicesMode(node) {
    state.mode = Mode.CHOICES;
    state.choiceLocked = false;
    state.choiceDuration = Number(state.story.choiceDurationSec) || 5.0;
    state.choiceRemaining = state.choiceDuration;
    syncAllAudioStates();

    dom.stageScrim.classList.add('is-dimmed');
    dom.choiceStepBadge.textContent = `抉择 ${node.choiceIndex || ''} / 4`;
    dom.choicePrompt.textContent = node.prompt || '请做出你的选择：';
    dom.optionATitle.textContent = node.optionA;
    dom.optionASub.textContent = node.optionASub || '';
    dom.optionBTitle.textContent = node.optionB;
    dom.optionBSub.textContent = node.optionBSub || '';

    dom.btnOptionA.classList.remove('is-selected');
    dom.btnOptionB.classList.remove('is-selected');
    dom.btnChoicePrev.classList.toggle('hidden', state.history.length === 0);

    updateCountdownVisual();
    dom.choiceLayer.classList.remove('hidden');

    // 与 Unity 版 choicePainted 一致：首帧渲染上屏后再正式启动 5 秒倒计时
    requestAnimationFrame(() => {
      if (state.mode !== Mode.CHOICES) return;
      state.choiceLastTs = performance.now();
      state.choiceRafId = requestAnimationFrame(tickChoiceClock);
    });
  }

  function stopChoiceClock() {
    if (state.choiceRafId) {
      cancelAnimationFrame(state.choiceRafId);
      state.choiceRafId = 0;
    }
  }

  function updateCountdownVisual() {
    const ratio = Math.max(0, Math.min(1, state.choiceRemaining / state.choiceDuration));
    dom.countdownFill.style.transform = `scaleX(${ratio.toFixed(4)})`;
    dom.countdownSeconds.textContent = `${state.choiceRemaining.toFixed(1)}s`;
  }

  function tickChoiceClock(now) {
    if (state.mode !== Mode.CHOICES || state.choiceLocked) return;
    const rawDelta = Math.max(0, (now - state.choiceLastTs) / 1000);
    state.choiceLastTs = now;

    const clockPaused = state.paused || state.treeOpen || document.hidden;
    if (!clockPaused) {
      state.choiceRemaining = Math.max(0, state.choiceRemaining - Math.min(rawDelta, 0.25));
      updateCountdownVisual();
      if (state.choiceRemaining <= 0) {
        // 5 秒倒计时归零，按规则自动锁定并跳转分支 A
        chooseBranch(0, false);
        return;
      }
    }
    state.choiceRafId = requestAnimationFrame(tickChoiceClock);
  }

  function chooseBranch(optionIndex, fromUserGesture) {
    if (state.mode !== Mode.CHOICES || state.choiceLocked || state.paused || state.treeOpen) return;
    const node = state.nodeMap.get(state.currentNodeId);
    if (!node || node.ending || node.next) return;

    state.choiceLocked = true;
    stopChoiceClock();

    const chosenBtn = optionIndex === 0 ? dom.btnOptionA : dom.btnOptionB;
    chosenBtn.classList.add('is-selected');

    const targetId = optionIndex === 0 ? node.targetA : node.targetB;
    state.history.push({
      node: node.id,
      option: optionIndex,
      target: targetId
    });

    playNode(targetId, { restoreChoice: false, fromUserGesture });
  }

  /* ==========================================================================
     结局成就结算、分支回溯与剧情树跳转
     ========================================================================== */

  function countUnlockedBranches() {
    const branchIds = ['02a', '02b', '04a', '04b', '06a', '06b', '08a', '08b'];
    return branchIds.filter((id) => state.visitedNodes.has(id)).length;
  }

  function enterEndingMode(node) {
    state.mode = Mode.ENDING;
    syncAllAudioStates();

    const routeCode = state.history.map((h) => (h.option === 0 ? 'A' : 'B')).join('');
    if (routeCode.length === 4) {
      state.completedRoutes.add(routeCode);
      saveMetaPreferences();
    }

    dom.stageScrim.classList.add('is-dimmed');
    dom.endingAchievement.textContent = `达成成就：${node.endingAchievement || '直播救场！职位晋升！'}`;
    dom.endingTitle.textContent = node.endingTitle || '救场女王';
    dom.endingSubtitle.textContent = node.endingSubtitle || '';
    dom.endingCollectionStat.textContent =
      `已解锁分支 ${countUnlockedBranches()}/8 · 路线 ${state.completedRoutes.size}/16`;

    // 渲染 4 个可点击回溯的抉择轨迹胶囊
    dom.endingRouteChips.innerHTML = '';
    state.history.forEach((rec, idx) => {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'route-chip';
      const letter = rec.option === 0 ? 'A' : 'B';
      btn.textContent = `抉择${idx + 1} · ${rec.target.toUpperCase()}`;
      btn.title = `点击回溯至节点 ${rec.node} 重新选择（当前选 ${letter}）`;
      btn.addEventListener('click', () => jumpBackToHistoryIndex(idx));
      dom.endingRouteChips.appendChild(btn);
    });

    dom.btnEndingBack.disabled = state.history.length === 0;
    dom.endingLayer.classList.remove('hidden');
  }

  /**
   * 退回最近一次选择点（支持从结局 09 依次退回 07 → 05 → 03 → 01）。
   */
  function stepBackOneChoice() {
    if (state.history.length === 0) return;
    jumpBackToHistoryIndex(state.history.length - 1);
  }

  function jumpBackToHistoryIndex(historyIndex) {
    if (historyIndex < 0 || historyIndex >= state.history.length) return;
    const targetChoiceNodeId = state.history[historyIndex].node;
    state.history = state.history.slice(0, historyIndex);
    closeModals(false);
    playNode(targetChoiceNodeId, { restoreChoice: true, fromUserGesture: true });
  }

  /* ==========================================================================
     暂停设置、剧情分支图与首页流转
     ========================================================================== */

  function setPaused(paused) {
    if (!state.sessionActive) return;
    if (state.mode === Mode.MENU || state.mode === Mode.ERROR) return;

    state.paused = paused;
    const activeSlot = slots[state.activeSlotIndex];

    if (paused) {
      if (activeSlot && state.mode === Mode.PLAYING) {
        activeSlot.el.pause();
      }
      dom.btnPauseBack.disabled = state.history.length === 0;
      dom.pauseModal.classList.remove('hidden');
    } else {
      dom.pauseModal.classList.add('hidden');
      state.choiceLastTs = performance.now();
      if (activeSlot && state.mode === Mode.PLAYING) {
        enforceNormalRate(activeSlot.el);
        applyAudioStateToElement(activeSlot.el, true);
        activeSlot.el.play().catch(() => {});
      }
    }
  }

  function openStoryTree() {
    if (!state.sessionActive) return;
    state.treeOpen = true;
    const activeSlot = slots[state.activeSlotIndex];
    if (activeSlot && state.mode === Mode.PLAYING) {
      activeSlot.el.pause();
    }
    dom.pauseModal.classList.add('hidden');
    renderStoryGraph();
    dom.treeModal.classList.remove('hidden');
  }

  function closeStoryTree() {
    if (!state.treeOpen) return;
    state.treeOpen = false;
    dom.treeModal.classList.add('hidden');
    state.choiceLastTs = performance.now();
    if (!state.paused && state.mode === Mode.PLAYING) {
      const activeSlot = slots[state.activeSlotIndex];
      if (activeSlot) {
        enforceNormalRate(activeSlot.el);
        applyAudioStateToElement(activeSlot.el, true);
        activeSlot.el.play().catch(() => {});
      }
    }
  }

  function closeModals(resumeIfPlaying = true) {
    dom.pauseModal.classList.add('hidden');
    dom.treeModal.classList.add('hidden');
    state.treeOpen = false;
    if (resumeIfPlaying && state.paused) {
      setPaused(false);
    } else {
      state.paused = false;
    }
  }

  function renderStoryGraph() {
    dom.treeProgressSummary.textContent =
      `已解锁分支 ${countUnlockedBranches()} / 8 · 点击本局已途经的选择节点可回溯重选`;
    dom.storyGraph.innerHTML = '';

    const layoutRows = [
      ['01'],
      ['02a', '02b'],
      ['03'],
      ['04a', '04b'],
      ['05'],
      ['06a', '06b'],
      ['07'],
      ['08a', '08b'],
      ['09']
    ];

    layoutRows.forEach((rowIds) => {
      const rowEl = document.createElement('div');
      rowEl.className = rowIds.length === 1 ? 'graph-row-main' : 'graph-row-branch';

      rowIds.forEach((id) => {
        const node = state.nodeMap.get(id);
        if (!node) return;
        const historyIdx = state.history.findIndex((h) => h.node === id);
        const isCurrent = state.currentNodeId === id;
        const isVisited = state.visitedNodes.has(id) || isCurrent;
        const canJump = historyIdx !== -1;

        const item = document.createElement(canJump ? 'button' : 'div');
        if (canJump) item.type = 'button';
        item.className = 'graph-node';
        if (isVisited) item.classList.add('is-visited');
        if (isCurrent) item.classList.add('is-current');
        if (canJump) item.classList.add('is-jumpable');

        const titleSpan = document.createElement('span');
        titleSpan.textContent = isVisited ? node.title : `${id.toUpperCase()} · 未解锁`;
        item.appendChild(titleSpan);

        if (isCurrent) {
          const tag = document.createElement('span');
          tag.className = 'graph-tag';
          tag.textContent = '当前';
          item.appendChild(tag);
        } else if (canJump) {
          const tag = document.createElement('span');
          tag.className = 'graph-tag';
          tag.textContent = '可回溯';
          item.appendChild(tag);
          item.addEventListener('click', () => jumpBackToHistoryIndex(historyIdx));
        }

        rowEl.appendChild(item);
      });

      dom.storyGraph.appendChild(rowEl);
    });
  }

  function returnToCoverMenu() {
    state.opToken += 1;
    stopChoiceClock();
    hideDeferredLoading();
    state.sessionActive = false;
    state.paused = false;
    state.treeOpen = false;
    state.audioBlockedByPolicy = false;
    state.mode = Mode.MENU;

    // 立即静音并停止全部视频槽，恢复首屏零声音状态
    slots.forEach((slot) => {
      slot.el.pause();
      slot.el.muted = true;
      slot.el.volume = 0;
      slot.el.classList.remove('is-active');
    });
    state.activeSlotIndex = -1;
    clearFreezeCanvas();

    dom.hudTop.classList.add('hidden');
    dom.choiceLayer.classList.add('hidden');
    dom.endingLayer.classList.add('hidden');
    dom.pauseModal.classList.add('hidden');
    dom.treeModal.classList.add('hidden');
    dom.errorModal.classList.add('hidden');
    dom.stageScrim.classList.remove('is-dimmed');
    dom.coverLayer.classList.remove('hidden');

    refreshCoverContinueButton();
    primeFirstVideoSilently();
  }

  function showError(msg) {
    stopChoiceClock();
    hideDeferredLoading();
    state.mode = Mode.ERROR;
    slots.forEach((s) => s.el.pause());
    dom.errorMessage.textContent = msg;
    dom.errorModal.classList.remove('hidden');
  }

  /* ==========================================================================
     首屏静默预缓冲与开局入口
     ========================================================================== */

  function primeFirstVideoSilently() {
    if (!state.story) return;
    const startNode = state.nodeMap.get(state.story.startNode);
    if (!startNode) return;

    const slot0 = slots[0];
    assignSlotSource(slot0, startNode);
    slot0.el.muted = true;
    slot0.el.volume = 0;

    const markReady = () => {
      dom.coverStatusDot.classList.add('is-ready');
      dom.coverStatusText.textContent = '首段已就绪';
      setTimeout(() => {
        if (dom.coverStatusPill) dom.coverStatusPill.classList.add('is-faded');
      }, 900);
    };

    if (slot0.el.readyState >= 3) {
      markReady();
    } else {
      if (dom.coverStatusPill) dom.coverStatusPill.classList.remove('is-faded');
      dom.coverStatusDot.classList.remove('is-ready');
      dom.coverStatusText.textContent = '预载中…';
      slot0.el.addEventListener('canplay', markReady, { once: true });
    }
  }

  function startNewGame() {
    if (!state.story) return;
    state.sessionActive = true;
    state.audioBlockedByPolicy = false;
    state.history = [];
    state.currentNodeId = state.story.startNode;
    playNode(state.story.startNode, { restoreChoice: false, fromUserGesture: true });
  }

  function continueSavedGame() {
    const saved = readValidSave();
    if (!saved) {
      startNewGame();
      return;
    }
    state.sessionActive = true;
    state.audioBlockedByPolicy = false;
    state.history = saved.history;
    state.currentNodeId = saved.currentNode;
    playNode(saved.currentNode, { restoreChoice: false, fromUserGesture: true });
  }

  /* ==========================================================================
     交互事件绑定与快捷键支持
     ========================================================================== */

  function bindEvents() {
    // 首页海报点击引导：点在主按钮上立即开局；点在海报空白处闪烁提示主按钮位置
    dom.btnStartHotspot.addEventListener('click', (e) => {
      e.stopPropagation();
      startNewGame();
    });

    dom.btnContinueGame.addEventListener('click', (e) => {
      e.stopPropagation();
      continueSavedGame();
    });

    dom.coverLayer.addEventListener('click', () => {
      dom.btnStartHotspot.classList.remove('is-guided');
      void dom.btnStartHotspot.offsetWidth;
      dom.btnStartHotspot.classList.add('is-guided');
    });

    // 顶部控制栏
    dom.btnToggleMute.addEventListener('click', () => {
      state.userMuted = !state.userMuted;
      if (!state.userMuted && state.volume <= 0) {
        state.volume = 1.0;
      }
      state.audioBlockedByPolicy = false;
      const activeSlot = slots[state.activeSlotIndex];
      if (activeSlot) activeSlot.blessed = true;
      syncAllAudioStates();
      saveMetaPreferences();
    });

    dom.btnUnlockAudio.addEventListener('click', () => {
      state.audioBlockedByPolicy = false;
      state.userMuted = false;
      if (state.volume <= 0) state.volume = 1.0;
      const activeSlot = slots[state.activeSlotIndex];
      if (activeSlot) {
        activeSlot.blessed = true;
        applyAudioStateToElement(activeSlot.el, true);
        activeSlot.el.play().catch(() => {});
      }
      syncAllAudioStates();
      saveMetaPreferences();
    });

    dom.btnNodeIndicator.addEventListener('click', () => openStoryTree());
    dom.btnOpenTree.addEventListener('click', () => openStoryTree());
    dom.btnPause.addEventListener('click', () => setPaused(true));

    // 分支抉择按钮
    dom.btnOptionA.addEventListener('click', () => chooseBranch(0, true));
    dom.btnOptionB.addEventListener('click', () => chooseBranch(1, true));
    dom.btnChoicePrev.addEventListener('click', () => stepBackOneChoice());
    dom.btnChoiceReplay.addEventListener('click', () => {
      playNode(state.currentNodeId, { restoreChoice: false, fromUserGesture: true });
    });

    // 结局结算按钮
    dom.btnEndingBack.addEventListener('click', () => stepBackOneChoice());
    dom.btnEndingRestart.addEventListener('click', () => startNewGame());
    dom.btnEndingHome.addEventListener('click', () => returnToCoverMenu());

    // 暂停菜单
    dom.btnClosePause.addEventListener('click', () => setPaused(false));
    dom.btnResume.addEventListener('click', () => setPaused(false));
    dom.btnReplayCurrent.addEventListener('click', () => {
      closeModals(false);
      playNode(state.currentNodeId, { restoreChoice: false, fromUserGesture: true });
    });
    dom.btnPauseBack.addEventListener('click', () => stepBackOneChoice());
    dom.btnPauseTree.addEventListener('click', () => openStoryTree());
    dom.btnPauseHome.addEventListener('click', () => returnToCoverMenu());

    dom.volumeSlider.addEventListener('input', () => {
      const val = Number(dom.volumeSlider.value) / 100;
      state.volume = Math.max(0, Math.min(1, val));
      state.userMuted = state.volume <= 0;
      state.audioBlockedByPolicy = false;
      syncAllAudioStates();
      saveMetaPreferences();
    });

    if (document.fullscreenEnabled && dom.stage.requestFullscreen) {
      dom.btnFullscreen.classList.remove('hidden');
      dom.btnFullscreen.addEventListener('click', () => {
        if (!document.fullscreenElement) {
          document.documentElement.requestFullscreen().catch(() => {});
        } else {
          document.exitFullscreen().catch(() => {});
        }
      });
    }

    // 剧情树弹窗与异常弹窗
    dom.btnCloseTree.addEventListener('click', () => closeStoryTree());
    dom.treeModal.addEventListener('click', (e) => {
      if (e.target === dom.treeModal) closeStoryTree();
    });
    dom.pauseModal.addEventListener('click', (e) => {
      if (e.target === dom.pauseModal) setPaused(false);
    });

    dom.btnErrorRetry.addEventListener('click', () => {
      dom.errorModal.classList.add('hidden');
      playNode(state.currentNodeId, { restoreChoice: false, fromUserGesture: true });
    });
    dom.btnErrorHome.addEventListener('click', () => returnToCoverMenu());

    // 标签页切后台时自动暂停视频与 5 秒倒计时，避免错失选择
    document.addEventListener('visibilitychange', () => {
      if (
        document.hidden &&
        state.sessionActive &&
        (state.mode === Mode.PLAYING || state.mode === Mode.CHOICES)
      ) {
        setPaused(true);
      }
    });

    // 桌面端键盘操作支持
    document.addEventListener('keydown', (e) => {
      if (e.metaKey || e.ctrlKey || e.altKey) return;
      const key = e.key.toLowerCase();

      if (state.mode === Mode.MENU) {
        if (key === 'enter' || key === ' ') {
          e.preventDefault();
          startNewGame();
        }
        return;
      }

      if (key === 'escape') {
        e.preventDefault();
        if (state.treeOpen) closeStoryTree();
        else if (state.mode === Mode.PLAYING || state.mode === Mode.CHOICES) {
          setPaused(!state.paused);
        }
        return;
      }

      if (key === ' ') {
        if (state.treeOpen) return;
        if (state.mode === Mode.PLAYING || state.mode === Mode.CHOICES) {
          e.preventDefault();
          setPaused(!state.paused);
        }
        return;
      }

      if (key === 'm') {
        e.preventDefault();
        dom.btnToggleMute.click();
        return;
      }

      if (state.mode === Mode.CHOICES && !state.paused && !state.treeOpen) {
        if (key === '1' || key === 'a') {
          e.preventDefault();
          chooseBranch(0, true);
        } else if (key === '2' || key === 'b') {
          e.preventDefault();
          chooseBranch(1, true);
        }
      }
    });
  }

  /* ==========================================================================
     初始化启动与诊断只读钩子
     ========================================================================== */

  async function bootstrap() {
    initVideoSlots();
    loadMetaPreferences();
    bindEvents();

    try {
      const story = await window.BeautyQueenStory.loadStoryConfig();
      state.story = story;
      state.nodeMap.clear();
      story.nodes.forEach((n) => state.nodeMap.set(n.id, n));
      state.currentNodeId = story.startNode;

      syncAllAudioStates();
      refreshCoverContinueButton();
      primeFirstVideoSilently();
    } catch (err) {
      showError('剧情配置文件校验未通过：\n' + (err ? err.message : String(err)));
    }
  }

  // 暴露只读运行态快照便于自动化测试与实机验收
  window.__BQ_V4_DIAG__ = {
    getState() {
      const active = slots[state.activeSlotIndex];
      return {
        mode: state.mode,
        sessionActive: state.sessionActive,
        currentNodeId: state.currentNodeId,
        paused: state.paused,
        treeOpen: state.treeOpen,
        choiceRemaining: state.choiceRemaining,
        history: state.history.map((h) => ({ ...h })),
        allVideosPausedAndSilent: slots.every(
          (s) => s.el.paused && (s.el.muted || s.el.volume === 0)
        ),
        activeVideo: active
          ? {
              slotIndex: active.index,
              nodeId: active.nodeId,
              paused: active.el.paused,
              muted: active.el.muted,
              volume: active.el.volume,
              playbackRate: active.el.playbackRate,
              defaultPlaybackRate: active.el.defaultPlaybackRate,
              currentTime: active.el.currentTime,
              duration: active.el.duration,
              readyState: active.el.readyState
            }
          : null
      };
    }
  };

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', bootstrap);
  } else {
    bootstrap();
  }
})();
