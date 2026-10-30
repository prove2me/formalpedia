-- Prove2me | Definitions.Def_CubicTurning_foundations
-- name    : CubicTurning_foundations
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:19:35.765982+00:00
-- url     : https://prove2.me/theorems/886edd46-89ed-4f21-800c-9e6b6b9d561e
-- title:
--   Cubic forward frames, signed energies, moments, and labelled laws
-- statement:
--   For complex $e,d_0,d_1$, a forward axis satisfies $|e|=1$ and $\operatorname{Re}(ed_0),\operatorname{Re}(ed_1)\ge0$. Define $h(e,d)=\operatorname{Im}(ed)/(|d|+\operatorname{Re}(ed))$ with total real division, so a zero denominator gives zero. The active event is $h(e,d_0)\ge1/7$, $h(e,d_1)\le-1/7$, or the same inequalities with the two displacements exchanged. All thresholds are non-strict. The pair energy is $B(d_0,d_1)=2(|d_0||d_1|-\operatorname{Re}(d_0\overline{d_1}))$; the selected energy $E$ is $B$ on the active event and zero otherwise. The original half-angle energy $A$ is $(|d_0|+\operatorname{Re}(ed_0))(|d_1|+\operatorname{Re}(ed_1))(h(e,d_0)-h(e,d_1))^2$ on the same event and zero otherwise. These functions are defined for arbitrary complex arguments; forwardness is a separate predicate.
--
--   For any real $r$ and complex endpoint $v$, let $m_r(v)=r$ if $\operatorname{Re}v\ge0$ and $-r$ otherwise. The frame is $1$ if $r\le\operatorname{Re}v$, then $-1$ if $\operatorname{Re}v\le-r$, then $-\mathrm i$ if $\operatorname{Im}v\ge0$, and $\mathrm i$ otherwise, with the cases tested in that order. Endpoint energy is $E(f_r(v),m_r(v),v-m_r(v))$.
--
--   For a labelled complex triple $a,b,c$, define $V_0=(|a|^2+|b|^2+|c|^2)/3$, the centroid $u=(a+b+c)/3$, centered variance $V_c=(|a-u|^2+|b-u|^2+|c-u|^2)/3$, and anisotropy $H=|((a-u)^2+(b-u)^2+(c-u)^2)/3|$. The complex sum is formed before taking its modulus.
--
--   An affine uniform forward law consists of three labelled actual derivative chains $z^{(i)}$ for $P(X)=(X-a)(X-b)(X-c)$ and unit forward axes $e_i$. Each chain satisfies $P''(z^{(i)}_0)=0$, $P'(z^{(i)}_1)=0$, and $P(z^{(i)}_2)=0$, starts at the prescribed $u$, and ends respectively at $a,b,c$. Its mean energy is $\overline E=\frac13\sum_{i=0}^2E(e_i,z^{(i)}_1-z^{(i)}_0,z^{(i)}_2-z^{(i)}_1)$. Repeated roots retain their labelled slots. This is finite equal-weight averaging, with no distinctness, independence, or greedy condition.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 11-11, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 13-14, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 136-137, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 16-19, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 227-227, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 309-313, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 374-380, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 382-384, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 475-475, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 477-478, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 480-481, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 65-66, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 68-70, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 9-9, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning

def IsForward (e d₀ d₁ : ℂ) : Prop := ‖e‖ = 1 ∧ 0 ≤ (e*d₀).re ∧ 0 ≤ (e*d₁).re

noncomputable def halfSlope (e d : ℂ) : ℝ := (e*d).im / (‖d‖ + (e*d).re)

noncomputable def pairEnergy (d₀ d₁ : ℂ) : ℝ :=
  2 * (‖d₀‖ * ‖d₁‖ - (d₀ * conj d₁).re)

noncomputable def energy (e d₀ d₁ : ℂ) : ℝ :=
  if (1/7 ≤ halfSlope e d₀ ∧ halfSlope e d₁ ≤ -(1/7)) ∨
     (1/7 ≤ halfSlope e d₁ ∧ halfSlope e d₀ ≤ -(1/7))
  then pairEnergy d₀ d₁ else 0













noncomputable def middle (r : ℝ) (v : ℂ) : ℂ :=
  if 0 ≤ v.re then (r:ℂ) else -(r:ℂ)

noncomputable def frame (r : ℝ) (v : ℂ) : ℂ :=
  if r ≤ v.re then 1 else if v.re ≤ -r then -1 else
  if 0 ≤ v.im then -Complex.I else Complex.I









noncomputable def endpointEnergy (r : ℝ) (v : ℂ) : ℝ :=
  energy (frame r v) (middle r v) (v-middle r v)









noncomputable def variance (a b c : ℂ) : ℝ := (‖a‖^2+‖b‖^2+‖c‖^2)/3













noncomputable def halfAngleEnergy (e d₀ d₁ : ℂ) : ℝ :=
  if (1/7 ≤ halfSlope e d₀ ∧ halfSlope e d₁ ≤ -(1/7)) ∨
     (1/7 ≤ halfSlope e d₁ ∧ halfSlope e d₀ ≤ -(1/7))
  then (‖d₀‖+(e*d₀).re)*(‖d₁‖+(e*d₁).re)*(halfSlope e d₀-halfSlope e d₁)^2
  else 0







structure AffineUniformForwardLaw (a b c u : ℂ) where
  paths : Fin 3 → Fin 3 → ℂ
  axes : Fin 3 → ℂ
  actual : ∀ i, DerivativeChainPrivate.IsChain ![a,b,c] (paths i)
  endpoint : ∀ i, paths i 2 = (![a,b,c] : Fin 3 → ℂ) i
  start : ∀ i, paths i 0 = u
  forward : ∀ i, IsForward (axes i) (paths i 1-paths i 0) (paths i 2-paths i 1)

noncomputable def AffineUniformForwardLaw.meanEnergy {a b c u : ℂ}
    (L : AffineUniformForwardLaw a b c u) : ℝ :=
  (∑ i, energy (L.axes i) (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1))/3







noncomputable def centroid (a b c : ℂ) : ℂ := (a+b+c)/3

noncomputable def centeredVariance (a b c : ℂ) : ℝ :=
  variance (a-centroid a b c) (b-centroid a b c) (c-centroid a b c)

noncomputable def anisotropy (a b c : ℂ) : ℝ :=
  ‖((a-centroid a b c)^2+(b-centroid a b c)^2+(c-centroid a b c)^2)/3‖






























end CubicTurning


