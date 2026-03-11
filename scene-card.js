import * as THREE from 'three';
import * as Spark from '@sparkjsdev/spark';

// ── DOM refs ──
const cardWrapper   = document.getElementById('card-wrapper');
const card          = document.getElementById('card');
const loadingScreen = document.getElementById('loading-screen');
const loadingText   = document.getElementById('loading-text');
const gyroBtn       = document.getElementById('gyro-btn');
const fsCloseBtn    = document.getElementById('fs-close-btn');
const fsFlash       = document.getElementById('fs-flash');

// ── Scene configurations ──
// layerZ: translateZ in px for each layer (scale compensation is auto-calculated)
// focalOffset: added to GEN_FOCAL_MM when computing camera vertical FOV
const SCENES = [
  {
    bg:          './files/scene1/BG-scene1.webp',
    mask:        './files/scene1/card-mask-alpha.webp',
    splat:       './files/3D/sharp_scene1.sog',
    camera:      './camera-scene.json',
    focalOffset:   0,
    fsFocalOffset: 0,  // 全屏模式下的焦距偏移（正值=缩小FOV=放大画面）
    splatX:      0,
    splatY:      0,
    splatZ:      -1,   // 沿 Z 轴平移 splat（正值=靠近相机，负值=远离相机）
    fsSplatZ:     0,   // 全屏模式下的 splat Z（独立调整）
    fsSplatScale: 1.0, // 全屏模式下的 splat 缩放（独立调整）
    haloColor:   'rgba(127, 0, 0, 0.75)',
    layers: [
      './files/scene1/layer1.webp',
      './files/scene1/layer2.webp',
      './files/scene1/layer3.webp',
      './files/scene1/layer4.webp',
      './files/scene1/layer5.webp',
      './files/scene1/layer6.webp',
      './files/scene1/layer7.webp',
      './files/scene1/layer8.webp',
      './files/scene1/layer9.webp',
      './files/scene1/layer10.webp',
    ],
    layerZ: [ 8, 24, 40, 56, 80, 70, 60, 50, 40, 30 ],
    pivotZ: -2,   // 旋转中心 Z 值（单位：Three.js 场景单位），-4 = 默认 -ORBIT_DIST
  },
  {
    bg:          './files/scene2/BG-scene2.webp',
    mask:        './files/scene2/card-mask-alpha.webp',
    splat:       './files/3D/sharp_scene2.sog',
    camera:      './camera-scene.json',
    focalOffset:   20,
    fsFocalOffset: 30, // 全屏模式下的焦距偏移（正值=缩小FOV=放大画面）
    splatX:      0.05,
    splatY:      0,
    splatZ:      -1,   // 沿 Z 轴平移 splat（正值=靠近相机，负值=远离相机）
    fsSplatZ:     0,   // 全屏模式下的 splat Z（独立调整）
    fsSplatScale: 1, // 全屏模式下的 splat 缩放（独立调整）
    haloColor:   'rgba(210, 127, 164, 0.65)',
    layers: [
      './files/scene2/layer1.webp',
      './files/scene2/layer2.webp',
      './files/scene2/layer3.webp',
      './files/scene2/layer4.webp',
    ],
    layerZ: [ 1, 25, 40, 50 ],
    pivotZ: -2,   // 旋转中心 Z 值（单位：Three.js 场景单位），-4 = 默认 -ORBIT_DIST
  },
];

// ── Camera constants ──
const GEN_FOCAL_MM = 30;
const PERSPECTIVE  = 900;   // must match CSS perspective value on #app
const ORBIT_DIST   = 4;
const SPLAT_SCALE  = 2;

// ── Interaction constants ──
const MAX_ORBIT_H   = 10 * Math.PI / 180;   // ±10° horizontal
const MAX_ORBIT_V   =  4 * Math.PI / 180;   // ±4° vertical
const DAMP          = 0.12;
const TOUCH_SENS    = 0.003;
const GYRO_SENS     = 0.5;
const CARD_TILT_AMP = 1.0;
const RAD_TO_DEG    = 180 / Math.PI;

// ── Fallback intrinsics (mirrors camera-scene.json) ──
const DEFAULT_INTRINSICS = [
  [1004.1146119075022, 0, 1024.0],
  [0, 1004.1146119075022, 1024.0],
  [0, 0, 1]
];

// ── State ──
let alpha = 0, beta = 0;
let touchDA = 0, touchDB = 0;
let gyroDA  = 0, gyroDB  = 0;
let targetA = 0, targetB = 0;
let dragging = false, lastX = 0, lastY = 0;
let downX = 0, downY = 0;
let gyroOn = false, gyroBeta0 = null, gyroGamma0 = null;
let renderer, scene, camera;
let loaded = false;
let currentSplatMesh = null;
let currentSceneIdx  = 0;
let switching        = false;
let activeGroupId    = 'a';   // which layer group is currently active

// ── Fullscreen state ──
let isFullscreen = false;
let _fsLock      = false;
let _lastTapTime = 0;
let _hadMultiTouch = false;

function clamp(v, lo, hi) { return v < lo ? lo : v > hi ? hi : v; }

// ── Compute vertical FOV from intrinsics ──
function computeVFOV(intrinsics, focalOffset) {
  const fy = intrinsics[1][1];
  const cy = intrinsics[1][2];
  const displayFocal = GEN_FOCAL_MM + focalOffset;
  const effectiveFy  = fy * (displayFocal / GEN_FOCAL_MM);
  return 2 * Math.atan(cy / effectiveFy) * 180 / Math.PI;
}

// ── Orbit frame (identity extrinsics: cam at origin, pivot at -Z) ──
const orbit = {
  cx: 0, cy: 0, cz: -ORBIT_DIST,
  radius: ORBIT_DIST,
  rx: 1, ry: 0, rz: 0,
  ux: 0, uy: 1, uz: 0,
  bx: 0, by: 0, bz: 1,
};

// ── 更新旋转中心 Z 值（pivotZ 为负值，如 -4 表示相机前方 4 单位） ──
function applyPivotZ(pivotZ) {
  const pz = pivotZ ?? -ORBIT_DIST;
  orbit.cz     = pz;
  orbit.radius = Math.abs(pz);
}

function applyOrbit(cam, a, b) {
  const cosA = Math.cos(-a), sinA = Math.sin(-a);
  const cosB = Math.cos(b),  sinB = Math.sin(b);
  const r = orbit.radius;
  const ox = r * (orbit.bx*cosA*cosB + orbit.rx*sinA*cosB + orbit.ux*sinB);
  const oy = r * (orbit.by*cosA*cosB + orbit.ry*sinA*cosB + orbit.uy*sinB);
  const oz = r * (orbit.bz*cosA*cosB + orbit.rz*sinA*cosB + orbit.uz*sinB);
  cam.position.set(orbit.cx + ox, orbit.cy + oy, orbit.cz + oz);
  cam.lookAt(orbit.cx, orbit.cy, orbit.cz);
}

// ── Load camera params ──
async function loadCameraParams(url) {
  try {
    const res = await fetch(url);
    if (!res.ok) return null;
    const data = await res.json();
    return data.intrinsics ? data : null;
  } catch { return null; }
}

// ── Apply scene assets to the specified (or active) layer group ──
function applySceneAssets(cfg, groupId = null) {
  const gId = groupId ?? activeGroupId;

  // Background — write to the matching bg div, ensure it's visible
  const bgEl = document.getElementById(`bg-${gId}`);
  bgEl.style.backgroundImage = `url('${cfg.bg}')`;
  bgEl.style.opacity         = '1';

  // Halo color
  document.getElementById('halo').style.background = cfg.haloColor;

  // Canvas mask
  const canvas = card.querySelector('canvas');
  if (canvas) {
    canvas.style.webkitMaskImage = `url('${cfg.mask}')`;
    canvas.style.maskImage       = `url('${cfg.mask}')`;
  }

  // Layers in the target group
  const group    = document.getElementById(`layers-${gId}`);
  const layerEls = group.querySelectorAll('.card-layer');
  layerEls.forEach((el, i) => {
    if (i < cfg.layers.length) {
      const z = cfg.layerZ[i] ?? 0;
      el.src             = cfg.layers[i];
      el.style.display   = 'block';
      el.style.filter    = '';
      el.style.transform = `translateZ(${z}px) scale(${(PERSPECTIVE - z) / PERSPECTIVE})`;
    } else {
      el.style.display   = 'none';
      el.style.transform = '';
      el.style.filter    = '';
    }
  });
}

// ── Init (scene 0) ──
async function init() {
  const cfg        = SCENES[0];
  const params     = await loadCameraParams(cfg.camera);
  const intrinsics = params?.intrinsics || DEFAULT_INTRINSICS;
  const vfov       = computeVFOV(intrinsics, cfg.focalOffset);

  // Create canvas inside #card
  const canvas = document.createElement('canvas');
  canvas.style.cssText = 'display:block;position:absolute;inset:0;width:100%;height:100%;pointer-events:none;';
  card.appendChild(canvas);

  const { width, height } = card.getBoundingClientRect();
  const w = Math.max(width,  1);
  const h = Math.max(height, 1);

  renderer = new THREE.WebGLRenderer({ canvas, alpha: true, antialias: false });
  renderer.setPixelRatio(window.devicePixelRatio);
  renderer.setSize(w, h);

  scene  = new THREE.Scene();
  camera = new THREE.PerspectiveCamera(vfov, w / h, 0.1, 1000);
  camera.position.set(0, 0, 0);
  camera.lookAt(0, 0, -ORBIT_DIST);

  // SparkRenderer
  const spark = new Spark.SparkRenderer({
    renderer,
    focalAdjustment: 1.0,
    minAlpha: 5 / 255,
  });
  scene.add(spark);

  // Load splat
  console.log(`[init] loading splat: ${cfg.splat}`);
  const splatMesh = new Spark.SplatMesh({
    url:      cfg.splat,
    fileType: 'pcsogszip',
  });
  splatMesh.quaternion.set(1, 0, 0, 0);
  splatMesh.position.set(cfg.splatX ?? 0, cfg.splatY ?? 0, cfg.splatZ ?? 0);
  scene.add(splatMesh);
  currentSplatMesh = splatMesh;

  await splatMesh.initialized;
  console.log(`[init] splat loaded: ${cfg.splat}, numSplats=${splatMesh.numSplats}`);
  splatMesh.scale.setScalar(SPLAT_SCALE);

  applyPivotZ(cfg.pivotZ);
  applySceneAssets(cfg);

  loaded = true;
  loadingScreen.classList.add('hidden');
}

// ── Switch scene with per-layer parallax animation ──
async function switchScene(idx) {
  if (idx === currentSceneIdx || switching) return;
  switching = true;

  // ── 0. 相机先归位（清除所有输入累积量，tick() 下一帧自动复位） ──
  touchDA = touchDB = gyroDA = gyroDB = 0;
  alpha   = 0;
  beta    = 0;

  const cfg        = SCENES[idx];
  const currentCfg = SCENES[currentSceneIdx];
  // dir = -1: scene1→scene2 (exit left / enter from right)
  // dir = +1: scene2→scene1 (exit right / enter from left)
  const dir       = idx > currentSceneIdx ? -1 : 1;
  const cardWidth = cardWrapper.getBoundingClientRect().width;
  const DURATION  = 850;   // ms
  const PARALLAX  = 24.0;  // parallax strength: z=8→×1.1, z=50→×1.67, z=80→×2.07

  const currentGroupId = activeGroupId;
  const nextGroupId    = activeGroupId === 'a' ? 'b' : 'a';
  const currentBgEl    = document.getElementById(`bg-${currentGroupId}`);
  const nextBgEl       = document.getElementById(`bg-${nextGroupId}`);

  // ── 1. 将下一场景图层预置在屏幕对侧（画面外） ──
  const nextGroup    = document.getElementById(`layers-${nextGroupId}`);
  const nextLayerEls = Array.from(nextGroup.querySelectorAll('.card-layer'));

  nextLayerEls.forEach((el, i) => {
    if (i < cfg.layers.length) {
      const z              = cfg.layerZ[i] ?? 0;
      const scale          = (PERSPECTIVE - z) / PERSPECTIVE;
      const parallaxFactor = 1 + (z / PERSPECTIVE) * PARALLAX;
      const startX         = -dir * cardWidth * parallaxFactor;
      el.src             = cfg.layers[i];
      el.style.display   = 'block';
      el.style.opacity   = '0';
      el.style.filter    = 'brightness(0)';
      el.style.transform = `translateX(${startX}px) translateZ(${z}px) scale(${scale})`;
    } else {
      el.style.display = 'none';
    }
  });

  // 等待新场景图片 + mask 预加载完成（mask 必须先加载完才能安全切换）
  const nextVisible = nextLayerEls.filter((_, i) => i < cfg.layers.length);
  const maskPreload = new Image();
  maskPreload.src   = cfg.mask;
  await Promise.all([
    ...nextVisible.map(img =>
      img.complete ? Promise.resolve() : new Promise(r => { img.onload = r; img.onerror = r; })
    ),
    maskPreload.decode().catch(() => {}),   // 预加载 mask，失败也继续
  ]);

  // 预置下一背景（不可见，等动画中渐显）
  nextBgEl.style.backgroundImage = `url('${cfg.bg}')`;
  nextBgEl.style.opacity         = '0';

  // ── 2. 并行：加载新 splat，canvas 将在 rAF 循环中渐出，splat 就绪后渐入 ──
  loaded = false;
  card.style.transition = 'none'; // 关闭 CSS transition，由 rAF 逐帧接管

  const haloEl            = document.getElementById('halo');
  let   splatReady        = false;   // splat 加载完成标志
  let   haloColorSwitched = false;
  // 'exit'  → canvas 正在随旧场景滑出
  // 'enter' → canvas 已不可见且 splat 就绪，开始随新场景滑入
  let   canvasState       = 'exit';

  const loadPromise = (async () => {
    if (currentSplatMesh) { scene.remove(currentSplatMesh); currentSplatMesh = null; }

    const params     = cfg.camera ? await loadCameraParams(cfg.camera) : null;
    const intrinsics = params?.intrinsics || DEFAULT_INTRINSICS;
    camera.fov = computeVFOV(intrinsics, cfg.focalOffset);
    camera.updateProjectionMatrix();
    applyPivotZ(cfg.pivotZ);
    // mask 切换由 rAF 在 canvas opacity=0 时统一处理，此处不提前替换

    console.log(`[switch→${idx}] loading splat: ${cfg.splat}`);
    const splatMesh = new Spark.SplatMesh({ url: cfg.splat, fileType: 'pcsogszip' });
    splatMesh.quaternion.set(1, 0, 0, 0);
    splatMesh.position.set(cfg.splatX ?? 0, cfg.splatY ?? 0, cfg.splatZ ?? 0);
    scene.add(splatMesh);
    currentSplatMesh = splatMesh;
    await splatMesh.initialized;
    console.log(`[switch→${idx}] splat loaded: ${cfg.splat}, numSplats=${splatMesh.numSplats}`);
    splatMesh.scale.setScalar(SPLAT_SCALE);

    // splat 就绪：仅恢复渲染，canvas 淡入由收尾动画统一负责
    loaded     = true;
    splatReady = true;
  })();

  // ── 3. 视差逐帧动画：layers / bg / canvas / halo 全部在此同步 ──
  const currentGroup    = document.getElementById(`layers-${currentGroupId}`);
  const currentLayerEls = Array.from(currentGroup.querySelectorAll('.card-layer'))
                               .filter(el => el.style.display !== 'none');

  const animPromise = new Promise(resolve => {
    const startTime = performance.now();

    function frame(now) {
      const rawT = Math.min((now - startTime) / DURATION, 1);
      // 三次缓入缓出（位移用）
      const t = rawT < 0.5
        ? 4 * rawT ** 3
        : 1 - (-2 * rawT + 2) ** 3 / 2;

      // 统一 opacity 曲线（rawT 线性）
      const exitOpacity  = Math.max(0, 1 - rawT * 1.6);         // 0 at rawT≈0.625
      const enterOpacity = Math.min(1, Math.max(0, (rawT - 0.38) / 0.62));  // 38%→100%

      // ── 退出：layers + bg + halo + canvas（splat未就绪时） ──
      currentLayerEls.forEach((el, i) => {
        const z              = currentCfg.layerZ[i] ?? 0;
        const scale          = (PERSPECTIVE - z) / PERSPECTIVE;
        const parallaxFactor = 1 + (z / PERSPECTIVE) * PARALLAX;
        const tx             = dir * t * cardWidth * parallaxFactor;
        el.style.transform = `translateX(${tx}px) translateZ(${z}px) scale(${scale})`;
        el.style.opacity   = String(exitOpacity);
        el.style.filter    = `brightness(${1 - t * 0.85})`;
      });

      currentBgEl.style.opacity = String(exitOpacity);

      // canvas 状态机：退出 / 入场均在同一 rAF 内完成，位移与 layers 完全同步（相同 t）
      // 退出比 layers 更快渐隐（rawT*3 → 0 at rawT≈0.33）
      // 入场比 layers 更慢渐显（rawT 0.6→1.0，layers 是 0.38→1.0）
      const cpf = 1 + (50 / PERSPECTIVE) * PARALLAX;
      if (canvasState === 'exit') {
        const canvasExitOp = Math.max(0, 1 - rawT * 4.0);
        card.style.opacity   = String(canvasExitOp);
        card.style.transform = `translateX(${dir * t * cardWidth * cpf}px) translateZ(0px)`;
        // canvas 完全不可见 + splat 已就绪 → 切换入场状态，瞬间跳到对侧（不可见）
        if (canvasExitOp === 0 && splatReady) {
          canvasState = 'enter';
          // 此刻 opacity=0，安全替换 mask（图片已预加载，无闪烁）
          const canvasEl = card.querySelector('canvas');
          if (canvasEl) {
            canvasEl.style.webkitMaskImage = `url('${cfg.mask}')`;
            canvasEl.style.maskImage       = `url('${cfg.mask}')`;
          }
          card.style.transform = `translateX(${-dir * cardWidth * cpf}px) translateZ(0px)`;
        }
      } else {
        // 入场：从对侧滑入，与 nextVisible layers 使用完全相同的 t
        const canvasEnterOp = Math.min(1, Math.max(0, (rawT - 0.6) / 0.4));
        card.style.opacity   = String(canvasEnterOp);
        card.style.transform = `translateX(${-dir * cardWidth * cpf * (1 - t)}px) translateZ(0px)`;
      }

      // halo：前半程用退出 opacity，后半程切换颜色并用入场 opacity
      if (rawT >= 0.5 && !haloColorSwitched) {
        haloEl.style.background = cfg.haloColor;
        haloColorSwitched = true;
      }
      haloEl.style.opacity = String(rawT < 0.5 ? exitOpacity : enterOpacity);

      // ── 入场：layers + bg ──
      nextVisible.forEach((el, i) => {
        const z              = cfg.layerZ[i] ?? 0;
        const scale          = (PERSPECTIVE - z) / PERSPECTIVE;
        const parallaxFactor = 1 + (z / PERSPECTIVE) * PARALLAX;
        const startX         = -dir * cardWidth * parallaxFactor;
        const tx             = startX * (1 - t);
        el.style.transform = `translateX(${tx}px) translateZ(${z}px) scale(${scale})`;
        el.style.opacity   = String(enterOpacity);
        el.style.filter    = `brightness(${t})`;
      });

      nextBgEl.style.opacity = String(enterOpacity);

      if (rawT < 1) {
        requestAnimationFrame(frame);
      } else {
        resolve();
      }
    }

    requestAnimationFrame(frame);
  });

  // 等待动画 + splat 加载同时完成（splat 加载失败时记录错误，动画仍正常收尾）
  let splatLoadFailed = false;
  await Promise.all([
    animPromise,
    loadPromise.catch(err => {
      console.error('[scene-card] splat load failed:', err);
      splatLoadFailed = true;
    }),
  ]);

  // ── 4. 收尾：重置所有临时样式 ──

  // 隐藏旧场景图层
  currentLayerEls.forEach(el => {
    el.style.display   = 'none';
    el.style.opacity   = '';
    el.style.filter    = '';
    el.style.transform = '';
  });

  // 将新场景图层归位（去掉 translateX 和临时样式）
  nextVisible.forEach((el, i) => {
    const z = cfg.layerZ[i] ?? 0;
    el.style.transform = `translateZ(${z}px) scale(${(PERSPECTIVE - z) / PERSPECTIVE})`;
    el.style.opacity   = '';
    el.style.filter    = '';
  });

  // bg 状态确认（动画结束时已是正确值，显式写入保证稳定）
  currentBgEl.style.opacity = '0';
  nextBgEl.style.opacity    = '1';

  // halo：清除 inline opacity（动画已将其置 1）
  haloEl.style.opacity = '';

  // ── canvas 兜底：splat 加载较慢时 canvas 未在 rAF 内完成入场，快速淡入 ──
  // 确保 mask 已切换（rAF 内未触发 canvasState='enter' 时的兜底）
  if (canvasState === 'exit') {
    const canvasEl = card.querySelector('canvas');
    if (canvasEl) {
      canvasEl.style.webkitMaskImage = `url('${cfg.mask}')`;
      canvasEl.style.maskImage       = `url('${cfg.mask}')`;
    }
  }
  const curOp = parseFloat(card.style.opacity) || 0;
  if (curOp < 0.99) {
    card.style.transform  = 'translateZ(0px)';    // 确保位置已归中
    card.style.transition = 'opacity 0.3s ease';  // 恢复 CSS transition 做淡入
    card.offsetWidth;                              // force reflow
    card.style.opacity = '1';
    await new Promise(r => setTimeout(r, 320));
  }

  // 清除所有 inline 样式，还原 CSS 定义的初始状态
  card.style.transition = '';
  card.style.transform  = '';
  card.style.opacity    = '';

  // splat 加载失败时回退到原场景，确保 switching 一定被复位
  if (splatLoadFailed) {
    activeGroupId = currentGroupId;
    // currentSceneIdx 保持不变（留在原场景）
  } else {
    activeGroupId   = nextGroupId;
    currentSceneIdx = idx;
  }
  loaded    = true;
  switching = false;
}

// ── Fullscreen enter / exit ──
function enterFullscreen() {
  if (isFullscreen || _fsLock || !loaded || switching) return;
  _fsLock = true;

  // Phase 1: flash in (cinematic cut)
  fsFlash.classList.add('active');

  setTimeout(() => {
    // Phase 2: expand card to full screen
    isFullscreen = true;
    document.body.classList.add('scene-fullscreen');

    // Apply fullscreen-specific FOV / splat Z / scale for current scene
    const cfg = SCENES[currentSceneIdx];
    if (cfg.fsFocalOffset) {
      camera.fov = computeVFOV(DEFAULT_INTRINSICS, cfg.fsFocalOffset);
      camera.updateProjectionMatrix();
    }
    if (currentSplatMesh) {
      currentSplatMesh.position.z = cfg.fsSplatZ ?? cfg.splatZ ?? 0;
      currentSplatMesh.scale.setScalar(SPLAT_SCALE * (cfg.fsSplatScale ?? 1.0));
    }

    // Reset orbit to neutral so scene starts centered
    touchDA = touchDB = 0;
    alpha = beta = targetA = targetB = 0;

    // Phase 3: flash out
    fsFlash.classList.remove('active');

    setTimeout(() => { _fsLock = false; }, 220);
  }, 180);
}

function exitFullscreen() {
  if (!isFullscreen || _fsLock) return;
  _fsLock = true;

  fsFlash.classList.add('active');

  setTimeout(() => {
    isFullscreen = false;
    document.body.classList.remove('scene-fullscreen');

    // Restore normal FOV / splat Z / scale for current scene
    const cfg = SCENES[currentSceneIdx];
    if (cfg.fsFocalOffset) {
      camera.fov = computeVFOV(DEFAULT_INTRINSICS, cfg.focalOffset ?? 0);
      camera.updateProjectionMatrix();
    }
    if (currentSplatMesh) {
      currentSplatMesh.position.z = cfg.splatZ ?? 0;
      currentSplatMesh.scale.setScalar(SPLAT_SCALE);
    }

    // Reset orbit so card returns to neutral tilt
    touchDA = touchDB = 0;
    alpha = beta = targetA = targetB = 0;

    fsFlash.classList.remove('active');

    setTimeout(() => { _fsLock = false; }, 220);
  }, 180);
}

// ── Render loop ──
function tick() {
  requestAnimationFrame(tick);
  if (!loaded) return;

  targetA = clamp(touchDA + gyroDA, -MAX_ORBIT_H, MAX_ORBIT_H);
  targetB = clamp(touchDB + gyroDB, -MAX_ORBIT_V, MAX_ORBIT_V);
  alpha  += (targetA - alpha) * DAMP;
  beta   += (targetB - beta)  * DAMP;

  applyOrbit(camera, alpha, beta);

  if (!isFullscreen) {
    const tiltY =  alpha * RAD_TO_DEG * CARD_TILT_AMP;
    const tiltX = -beta  * RAD_TO_DEG * CARD_TILT_AMP;
    cardWrapper.style.transform = `rotateX(${tiltX}deg) rotateY(${tiltY}deg)`;
  } else {
    cardWrapper.style.transform = '';
  }

  renderer.render(scene, camera);
}

requestAnimationFrame(tick);

// ── Touch / pointer interaction ──
cardWrapper.addEventListener('pointerdown', e => {
  dragging = true;
  lastX = e.clientX; lastY = e.clientY;
  downX = e.clientX; downY = e.clientY;
  e.preventDefault();
}, { passive: false });

cardWrapper.addEventListener('pointermove', e => {
  if (!dragging) return;
  touchDA = clamp(touchDA + (e.clientX - lastX) * TOUCH_SENS, -MAX_ORBIT_H, MAX_ORBIT_H);
  touchDB = clamp(touchDB + (e.clientY - lastY) * TOUCH_SENS, -MAX_ORBIT_V, MAX_ORBIT_V);
  lastX = e.clientX; lastY = e.clientY;
  e.preventDefault();
}, { passive: false });

cardWrapper.addEventListener('pointerup', e => {
  dragging = false;
  const dx = e.clientX - downX;
  const dy = e.clientY - downY;
  // Only treat as tap if pointer barely moved (not a drag)
  if (Math.sqrt(dx * dx + dy * dy) < 8 && e.pointerType !== 'touch') {
    const now = Date.now();
    if (now - _lastTapTime < 300) {
      _lastTapTime = 0;
      isFullscreen ? exitFullscreen() : enterFullscreen();
    } else {
      _lastTapTime = now;
    }
  }
});

cardWrapper.addEventListener('pointercancel', () => { dragging = false; });

// ── Double-tap (touch) detection ──
cardWrapper.addEventListener('touchstart', e => {
  if (e.touches.length >= 2) _hadMultiTouch = true;
}, { passive: true });

cardWrapper.addEventListener('touchend', e => {
  if (e.touches.length !== 0) return;
  if (_hadMultiTouch) { _hadMultiTouch = false; _lastTapTime = 0; return; }
  _hadMultiTouch = false;
  if (_fsLock || switching) return;
  const dx = (e.changedTouches[0]?.clientX ?? downX) - downX;
  const dy = (e.changedTouches[0]?.clientY ?? downY) - downY;
  if (Math.sqrt(dx * dx + dy * dy) >= 12) return; // was a drag, not a tap
  const now = Date.now();
  if (now - _lastTapTime < 300) {
    e.preventDefault();
    _lastTapTime = 0;
    isFullscreen ? exitFullscreen() : enterFullscreen();
  } else {
    _lastTapTime = now;
  }
}, { passive: false });

cardWrapper.addEventListener('touchcancel', () => {
  _hadMultiTouch = false; _lastTapTime = 0;
});

// ── Gyroscope ──
const isMobile = /Mobi|Android|iPhone|iPad|iPod/i.test(navigator.userAgent);
if (isMobile || 'DeviceOrientationEvent' in window) {
  gyroBtn.style.display = 'flex';
}

function onGyro(e) {
  if (!gyroOn || e.beta == null || e.gamma == null) return;
  if (gyroBeta0 == null) { gyroBeta0 = e.beta; gyroGamma0 = e.gamma; }
  gyroDA = clamp(-(e.gamma - gyroGamma0) * Math.PI / 180 * GYRO_SENS, -MAX_ORBIT_H, MAX_ORBIT_H);
  gyroDB = clamp(-(e.beta  - gyroBeta0)  * Math.PI / 180 * GYRO_SENS, -MAX_ORBIT_V, MAX_ORBIT_V);
}

gyroBtn.addEventListener('click', async () => {
  if (gyroOn) {
    gyroOn = false;
    gyroBtn.classList.remove('active');
    gyroDA = gyroDB = touchDA = touchDB = 0;
    window.removeEventListener('deviceorientation', onGyro);
    return;
  }
  if (typeof DeviceOrientationEvent?.requestPermission === 'function') {
    try {
      const perm = await DeviceOrientationEvent.requestPermission();
      if (perm !== 'granted') return;
    } catch { return; }
  }
  touchDA = touchDB = 0;
  gyroOn = true;
  gyroBeta0 = gyroGamma0 = null;
  gyroBtn.classList.add('active');
  window.addEventListener('deviceorientation', onGyro);
});

// ── Resize observer ──
new ResizeObserver(() => {
  if (!camera || !renderer) return;
  const { width, height } = card.getBoundingClientRect();
  if (!width || !height) return;
  renderer.setPixelRatio(window.devicePixelRatio);
  renderer.setSize(width, height);
  camera.aspect = width / height;
  camera.updateProjectionMatrix();
}).observe(card);

// ── Fullscreen close button & ESC key ──
fsCloseBtn.addEventListener('click', () => { exitFullscreen(); });

document.addEventListener('keydown', e => {
  if (e.key === 'Escape' && isFullscreen) exitFullscreen();
});

// ── Scene button selection ──
const sceneBtns = document.querySelectorAll('.scene-btn');
sceneBtns.forEach((btn, i) => {
  btn.addEventListener('pointerup', (e) => {
    e.stopPropagation();
    sceneBtns.forEach(b => {
      b.classList.remove('active');
      b.querySelector('.btn-overlay').src = './files/unselected.webp';
    });
    btn.classList.add('active');
    btn.querySelector('.btn-overlay').src = './files/selected.webp';
    switchScene(i);
  });
});

// ── Start ──
init().catch(err => {
  console.error('[scene-card] init failed:', err);
  loadingScreen.classList.add('hidden');
});
