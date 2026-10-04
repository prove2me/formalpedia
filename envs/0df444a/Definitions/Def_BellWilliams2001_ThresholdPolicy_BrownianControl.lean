-- Prove2me | Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl
-- name    : BellWilliams2001_ThresholdPolicy_BrownianControl
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:15:10.673122+00:00
-- url     : https://prove2.me/theorems/b855abc1-2807-4c6f-b990-5fa55d951afb
-- title:
--   The solution (41)–(42) of the Brownian control problem and its cost $J^*$ (44)
-- statement:
--   Let $\alpha_k^2$, $\beta_j^2$ be the variances of $\check u_k(1)$, $\check v_j(1)$ and set
--   $$\sigma_1^2=\lambda_1\alpha_1^2+\mu_1\beta_1^2+\beta_2^2(\lambda_1-\mu_1),\qquad \sigma_2^2=\lambda_2(\alpha_2^2+\beta_3^2).$$
--   On a probability space $(\Omega',\mathcal F',\mathbf P')$ let $B_1,B_2$ be independent standard Brownian motions and let $\tilde X_k(t)=\theta_kt+\sigma_kB_k(t)$, a two-dimensional Brownian motion started at the origin with drift $\theta$ and covariance $\mathrm{diag}(\sigma_1^2,\sigma_2^2)$ (Definition 4.1). With $y=(1,\mu_2/\mu_3)$ (39), the solution of the Brownian control problem is (41)–(42)
--   $$\tilde V^*(t)=-\inf_{0\le s\le t}\,y\cdot\tilde X(s),\quad \tilde W^*(t)=y\cdot\tilde X(t)+\tilde V^*(t),\quad \tilde Q^*=(0,\,y_2^{-1}\tilde W^*),\quad \tilde I^*=(0,\,\mu_2^{-1}\tilde V^*),$$
--   and its cost is (44)
--   $$J^*=\mathbf E\Big(\int_0^\infty e^{-\gamma t}\,h\cdot\tilde Q^*(t)\,dt\Big)\in[0,\infty].$$
--
--   $J^*$ is the benchmark of Theorem 5.3 and $(\tilde Q_2^*,\tilde I_2^*)$ the limit in Theorem 5.2.
--
--   **Formalization Note** $\tilde X$ is built from a pair of independent `IsBrownianReal` processes (time $\mathbb R_{\ge0}$, almost surely continuous paths); every two-dimensional Brownian motion with this drift and diagonal covariance has the law of such an $\tilde X$, and $J^*$ depends only on that law. The infimum in (41) is that of an almost surely continuous path on $[0,t]$; the cost is an iterated lower Lebesgue integral in $[0,\infty]$. $J^*$ is defined by (44), not by a closed form.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), pp. 619–620, Definition 4.1, (39), (41), (42), (44)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

/-- A pair `B = (B₁, B₂)` of **independent standard Brownian motions** on `(Ω', P')`: each `B k`
is a real Brownian motion indexed by `ℝ≥0` (Mathlib's `IsBrownianReal`, which includes
`B k 0 = 0` a.s. and a.s. continuous paths) and the two path-valued random elements are
independent. -/
structure IsBrownianPair {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    (B : Fin 2 → ℝ≥0 → Ω' → ℝ) : Prop where
  isProb : IsProbabilityMeasure P'
  brownian : ∀ k, IsBrownianReal (B k) P'
  indep : IndepFun (fun ω (t : ℝ≥0) => B 0 t ω) (fun ω (t : ℝ≥0) => B 1 t ω) P'

namespace SystemSequence

variable {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)

/-- `α_k²`, the squared coefficient of variation of `ǔ_k(i)` (its variance, since its mean is
one; (15), p. 615). -/
noncomputable def alphaSq (k : Fin 2) : ℝ := variance (M.uC k 1) M.P

/-- `β_j²`, the squared coefficient of variation of `v̌_j(i)` (its variance). -/
noncomputable def betaSq (j : Fin 3) : ℝ := variance (M.vC j 1) M.P

/-- The diagonal of the covariance matrix of `X̃` (p. 619):
`diag(λ₁α₁² + μ₁β₁² + β₂²(λ₁ − μ₁), λ₂(α₂² + β₃²))`. -/
noncomputable def sigmaSq (k : Fin 2) : ℝ :=
  if k = 0 then M.lam 0 * M.alphaSq 0 + M.mu 0 * M.betaSq 0 + M.betaSq 1 * (M.lam 0 - M.mu 0)
  else M.lam 1 * (M.alphaSq 1 + M.betaSq 2)

/-- `y = (1, μ₂/μ₃)` (39). -/
noncomputable def yvec (k : Fin 2) : ℝ :=
  if k = 0 then 1 else M.mu 1 / M.mu 2

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- The two-dimensional Brownian motion `X̃` of Definition 4.1 (p. 619), started at the origin,
with drift `θ = (θ₁, θ₂)` and diagonal covariance `diag(σ₁², σ₂²)`, built from a pair of
independent standard Brownian motions: `X̃_k(t) = θ_k t + σ_k B_k(t)`, `t ≥ 0`. -/
noncomputable def Xtilde (B : Fin 2 → ℝ≥0 → Ω' → ℝ) (ω : Ω') (t : ℝ) (k : Fin 2) : ℝ :=
  M.theta k * t + Real.sqrt (M.sigmaSq k) * B k t.toNNReal ω

/-- `Ṽ*(t) = −inf_{0 ≤ s ≤ t} y · X̃(s)` (41). (The path of `X̃` is continuous almost surely, so
the infimum is that of a continuous function on `[0,t]` off a null set.) -/
noncomputable def Vstar (B : Fin 2 → ℝ≥0 → Ω' → ℝ) (ω : Ω') (t : ℝ) : ℝ :=
  -(⨅ s : Set.Icc (0 : ℝ) t, ∑ k, M.yvec k * M.Xtilde B ω s k)

/-- `W̃*(t) = y · X̃(t) + Ṽ*(t)` (41), the one-dimensional reflected Brownian motion. -/
noncomputable def Wstar (B : Fin 2 → ℝ≥0 → Ω' → ℝ) (ω : Ω') (t : ℝ) : ℝ :=
  ∑ k, M.yvec k * M.Xtilde B ω t k + M.Vstar B ω t

/-- `Q̃*(t) = (0, y₂^{-1} W̃*(t))` (42). -/
noncomputable def Qstar (B : Fin 2 → ℝ≥0 → Ω' → ℝ) (ω : Ω') (t : ℝ) (k : Fin 2) : ℝ :=
  if k = 0 then 0 else M.Wstar B ω t / M.yvec 1

/-- `Ĩ*(t) = (0, μ₂^{-1} Ṽ*(t))` (42). -/
noncomputable def Istar (B : Fin 2 → ℝ≥0 → Ω' → ℝ) (ω : Ω') (t : ℝ) (k : Fin 2) : ℝ :=
  if k = 0 then 0 else M.Vstar B ω t / M.mu 1

/-- The optimal cost of the Brownian control problem (44):
`J* = E(∫₀^∞ e^{−γt} h · Q̃*(t) dt)`, an iterated lower Lebesgue integral in `[0,∞]`. -/
noncomputable def Jstar (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (Real.exp (-M.gamma * t) * ∑ k, M.h k * M.Qstar B ω t k) ∂volume ∂P'

end SystemSequence

end BellWilliams2001.ThresholdPolicy


