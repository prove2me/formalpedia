-- Prove2me | Definitions.Def_ChenWhitt93_Reflection_Supplement_AltRenewal
-- name    : ChenWhitt93_Reflection_Supplement_AltRenewal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:53:42.652687+00:00
-- url     : https://prove2.me/theorems/85693692-5678-4315-a8e9-4e6b8a99bdd1
-- title:
--   Section 5, pp. 354–355 — centred down time, the alternating-renewal context, the constants of (5.4), independent Brownian motions
-- statement:
--   This file fixes the objects of the alternating-renewal-process context of Section 5 of Chen and Whitt (1993). Each of $J$ stations alternates between up periods $u_1^j,u_2^j,\dots$ and down periods $d_1^j,d_2^j,\dots$, starting with an up period; $D_j(t)$ is the cumulative down time of station $j$ in $[0,t]$ (the published network model).
--
--   1. **Centred scaled down time.** For centring fractions $\nu=(\nu_1,\dots,\nu_J)$ and $n\ge1$,
--   $$
--   \hat D^n_j(t)=\frac{1}{\sqrt n}\Big[D_j(nt)-(1-\nu_j)nt\Big],\qquad t\ge0,
--   $$
--   the left-hand side of (5.1) and (5.3) (set to $0$ for $t<0$).
--   2. **Constants of Theorem 5.1.** With $u_j$, $d_j$ the mean up and down durations and $\sigma^2_{uj}$, $\sigma^2_{dj}$ their variances,
--   $$
--   \lambda_j=\frac{1}{d_j+u_j},\qquad \nu_j=\frac{u_j}{u_j+d_j},\qquad \sigma_j^2=\lambda_j(1-\lambda_jd_j)^2\sigma^2_{dj}+\lambda_j^3d_j^2\sigma^2_{uj}.
--   $$
--   Here $\lambda_j$ is the rate of up–down cycles, not the arrival rate of the network.
--   3. **Alternating-renewal context.** The durations do not depend on $n$; they are nonnegative random variables; the whole family $\{u_k^j,d_k^j: k\ge1,\ 1\le j\le J\}$ is mutually independent; for each $j$ the $u_k^j$ are identically distributed with mean $u_j$ and variance $\sigma^2_{uj}\in(0,\infty)$, and the $d_k^j$ are identically distributed with mean $d_j$ and variance $\sigma^2_{dj}\in(0,\infty)$.
--   4. **Independent standard Brownian motions.** $W=(W_1,\dots,W_J)$ has measurable coordinates, almost surely $W_j(0)=0$ and continuous paths on $[0,\infty)$, and for all $0\le s_0<s_1<\dots<s_m$ the increments $W_j(s_{i+1})-W_j(s_i)$ over all $i$ and $j$ are mutually independent centred Gaussians with variance $s_{i+1}-s_i$.
--
--   These objects state Theorem 5.1 and feed the hypothesis (5.1) of Theorem 5.2.
--
--   **Formalization Note** Durations are indexed from $0$, as in the published `Interruptions` structure. The page prints $c^2_{dj}$ in (5.4); the constant here uses $\sigma^2_{dj}$, as in (5.9) of the proof, and equals the classical value $(u_j^2\sigma^2_{dj}+d_j^2\sigma^2_{uj})/(u_j+d_j)^3$. The Brownian family is characterized through its finite-dimensional distributions plus continuity, which fixes its law on the evaluation σ-algebra.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), pp. 354–356, (5.1), (5.3), the alternating-renewal-process context before Theorem 5.1, (5.4) and (5.9)

import Mathlib
import Definitions.Def_ChenWhitt93_JumpDiffusion_Network

namespace ChenWhitt93.Reflection.Supplement

open MeasureTheory ProbabilityTheory Filter Topology
open ChenWhitt93.JumpDiffusion

/-!
Chen and Whitt (1993), Section 5, pp. 354–356: the centred, scaled cumulative down time of
(5.1)/(5.3), the alternating-renewal-process context of Theorem 5.1, its constants
`νⱼ = uⱼ/(uⱼ + dⱼ)`, `λⱼ = 1/(dⱼ + uⱼ)`, `σⱼ²` of (5.4)/(5.9), and a family of independent
standard Brownian motions. Up and down durations are indexed from `0` as in the published
`Interruptions` (`up j k` is the page's `u_{k+1}ʲ`); every station starts with an up period.
-/

/-- The left side of (5.1) and (5.3): `D̂ⱼⁿ(t) = n^{-1/2}[Dⱼ(nt) − (1 − νⱼ)nt]` for `t ≥ 0`,
where `Dⱼ` is the cumulative down time of station `j` of the up/down data `I` and `ν` the
centring fractions; extended by `0` to `t < 0`. -/
noncomputable def centredDown {J : ℕ} (I : Interruptions J) (nu : Fin J → ℝ) (n : ℕ) (t : ℝ) :
    Fin J → ℝ :=
  fun j => if t < 0 then 0 else (I.downTime j (n * t) - (1 - nu j) * n * t) / Real.sqrt n

/-- Theorem 5.1's `λⱼ = 1/(dⱼ + uⱼ)`, the rate of up–down cycles of station `j` (not the arrival
rate `λⱼ` of Sections 3–5). -/
noncomputable def cycleRate {J : ℕ} (u d : Fin J → ℝ) (j : Fin J) : ℝ :=
  1 / (d j + u j)

/-- Theorem 5.1's `νⱼ = uⱼ/(uⱼ + dⱼ)`, the long-run fraction of time station `j` is up. -/
noncomputable def upFraction {J : ℕ} (u d : Fin J → ℝ) (j : Fin J) : ℝ :=
  u j / (u j + d j)

/-- (5.4), read with `σ²_{dj}` as in (5.9): `σⱼ² = λⱼ(1 − λⱼdⱼ)²σ²_{dj} + λⱼ³dⱼ²σ²_{uj}` with
`λⱼ = 1/(dⱼ + uⱼ)`; `varU j = σ²_{uj}` and `varD j = σ²_{dj}` are the variances of an up and of
a down period. -/
noncomputable def downVarConst {J : ℕ} (u d varU varD : Fin J → ℝ) (j : Fin J) : ℝ :=
  cycleRate u d j * (1 - cycleRate u d j * d j) ^ 2 * varD j
    + cycleRate u d j ^ 3 * d j ^ 2 * varU j

/-- The alternating-renewal-process context of Theorem 5.1 (pp. 354–355) for random up/down data
`I ω` that do not depend on `n`: all durations are nonnegative random variables; the whole family
`{u_kʲ, d_kʲ : k ≥ 1, 1 ≤ j ≤ J}` is mutually independent; for each `j` the up periods are
identically distributed with mean `uⱼ` and variance `σ²_{uj} ∈ (0, ∞)`, and the down periods are
identically distributed with mean `dⱼ` and variance `σ²_{dj} ∈ (0, ∞)`. -/
def IsAltRenewal {J : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (I : Ω → Interruptions J) (u d varU varD : Fin J → ℝ) : Prop :=
  (∀ ω j k, 0 ≤ (I ω).up j k ∧ 0 ≤ (I ω).down j k) ∧
  (∀ j k, Measurable (fun ω => (I ω).up j k) ∧ Measurable (fun ω => (I ω).down j k)) ∧
  iIndepFun (fun (q : Fin J × ℕ × Bool) ω =>
    if q.2.2 then (I ω).up q.1 q.2.1 else (I ω).down q.1 q.2.1) P ∧
  (∀ j k, IdentDistrib (fun ω => (I ω).up j k) (fun ω => (I ω).up j 0) P P ∧
    IdentDistrib (fun ω => (I ω).down j k) (fun ω => (I ω).down j 0) P P) ∧
  ∀ j,
    MemLp (fun ω => (I ω).up j 0) 2 P ∧ P[fun ω => (I ω).up j 0] = u j ∧
      variance (fun ω => (I ω).up j 0) P = varU j ∧ 0 < varU j ∧
    MemLp (fun ω => (I ω).down j 0) 2 P ∧ P[fun ω => (I ω).down j 0] = d j ∧
      variance (fun ω => (I ω).down j 0) P = varD j ∧ 0 < varD j

/-- `W = (W₁, …, W_J)` is a family of `J` independent standard (mean 0, variance 1) Brownian
motions on `[0, ∞)`: every `Wⱼ(t)` is a random variable; almost surely `Wⱼ(0) = 0` and
`t ↦ Wⱼ(t)` is continuous on `[0, ∞)`; and for all times `0 ≤ s₀ < s₁ < ⋯ < s_m` the increments
`Wⱼ(s_{i+1}) − Wⱼ(sᵢ)`, over all `i < m` and all `j`, are mutually independent, each centred
Gaussian with variance `s_{i+1} − sᵢ`. (Values at `t < 0` are not constrained.) -/
def IsIndepStdBrownian {J : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : Ω → ℝ → Fin J → ℝ) : Prop :=
  (∀ t j, Measurable (fun ω => W ω t j)) ∧
  (∀ᵐ ω ∂P, ∀ j, W ω 0 j = 0 ∧ ContinuousOn (fun t => W ω t j) (Set.Ici 0)) ∧
  ∀ (m : ℕ) (s : Fin (m + 1) → ℝ), 0 ≤ s 0 → StrictMono s →
    iIndepFun (fun (p : Fin m × Fin J) ω => W ω (s p.1.succ) p.2 - W ω (s p.1.castSucc) p.2) P ∧
    ∀ (i : Fin m) (j : Fin J),
      P.map (fun ω => W ω (s i.succ) j - W ω (s i.castSucc) j) =
        gaussianReal 0 (s i.succ - s i.castSucc).toNNReal

end ChenWhitt93.Reflection.Supplement


