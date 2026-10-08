-- Prove2me | Definitions.Def_KurtzProtter91_Integrals_StepApprox
-- name    : KurtzProtter91_Integrals_StepApprox
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:59:18.976336+00:00
-- url     : https://prove2.me/theorems/ce0ef814-cbc0-4779-abb9-73190d3e9525
-- title:
--   Section 6, p. 1066 — the step approximation I_ε(z), its times τ_k(z), and the law of the thresholds θ_k
-- statement:
--   Let $E$ be a metric space with metric $r$, fix $\varepsilon>0$ and a sequence $\theta=(\theta_k)_{k\ge0}$ of thresholds. For a cadlag path $z\in D_E[0,\infty)$ define $\tau_0(z)=0$ and
--   $$\tau_{k+1}(z)=\inf\Big\{t>\tau_k(z):\ r\big(z(t),z(\tau_k(z))\big)\vee r\big(z(t-),z(\tau_k(z))\big)\ge\varepsilon\theta_k\Big\},$$
--   with $\inf\emptyset=\infty$, and set $\gamma_k(z)=z(\tau_k(z))$. The **step approximation** is
--   $$I_\varepsilon(z)(t)=\gamma_k(z)\qquad\text{for }\tau_k(z)\le t<\tau_{k+1}(z).$$
--   In the paper the $\theta_k$ are independent random variables uniformly distributed on $[\tfrac12,1]$, so $I_\varepsilon$ is a random map; here $\theta$ is an argument, $I^\theta_\varepsilon(z)$, and the law of $(\theta_k)$ is the infinite product of the uniform distribution on $[\tfrac12,1]$.
--
--   The step approximation replaces the integrand of Theorem 2.2 by a piecewise constant process that stays within $\varepsilon$ of it (§6, "Note that $r(z(t),I_\varepsilon(z)(t))\le\varepsilon$ for all $t$") and, by Lemma 6.1, converges jointly with it.
--
--   **Formalization Note** The times $\tau_k(z)$ take values in $[0,\infty]$ (`ℝ≥0∞`), so $\inf\emptyset=\infty$ is built in; once $\tau_k(z)=\infty$ every later time is $\infty$. For cadlag $z$ and $\theta_k\in[\tfrac12,1]$ the intervals $[\tau_k(z),\tau_{k+1}(z))$ partition $[0,\infty)$ and $I_\varepsilon(z)(t)$ is $\gamma_k(z)$ for the unique such $k$. For a path where no such $k$ exists (not cadlag) the value is the junk $z(t)$; the statements about $I_\varepsilon$ assume $z$ cadlag. The uniform law on $[\tfrac12,1]$ is $2\cdot$Lebesgue restricted to $[\tfrac12,1]$, a probability measure, so `Measure.infinitePi` is the genuine product.
-- source:
--   Kurtz and Protter, Weak Limit Theorems for Stochastic Integrals and Stochastic Differential Equations, Ann. Probab. 19 (1991), p. 1066, Section 6 (Uniform approximation by step functions)

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod

open Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace KurtzProtter91.Integrals

/-- The times `τ_k(z)` of §6, p. 1066, for a level `ε > 0` and thresholds `θ = (θ_k)`:
`τ_0(z) = 0` and
`τ_{k+1}(z) = inf {t > τ_k(z) : r(z(t), z(τ_k(z))) ∨ r(z(t −), z(τ_k(z))) ≥ ε θ_k}`,
valued in `[0, ∞]` with `inf ∅ = ∞`. (When `τ_k(z) = ∞` the set is empty, so `τ_{k+1}(z) = ∞`.) -/
noncomputable def stepTimes {E : Type*} [MetricSpace E] (ε : ℝ) (θ : ℕ → ℝ) (z : ℝ≥0 → E) :
    ℕ → ℝ≥0∞
  | 0 => 0
  | k + 1 =>
    sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) ''
      {t : ℝ≥0 | stepTimes ε θ z k < (t : ℝ≥0∞) ∧
        ε * θ k ≤ max (dist (z t) (z (stepTimes ε θ z k).toNNReal))
          (dist (leftLim z t) (z (stepTimes ε θ z k).toNNReal))})

open Classical in
/-- The step approximation `I_ε(z)` of §6, p. 1066: `I_ε(z)(t) = γ_k(z) = z(τ_k(z))` for
`τ_k(z) ≤ t < τ_{k+1}(z)`. For a cadlag `z` and `θ_k ∈ [½, 1]` the intervals
`[τ_k(z), τ_{k+1}(z))` partition `[0, ∞)`; if no such `k` exists (only possible for non-cadlag `z`)
the value is the junk `z(t)`. -/
noncomputable def stepApprox {E : Type*} [MetricSpace E] (ε : ℝ) (θ : ℕ → ℝ) (z : ℝ≥0 → E)
    (t : ℝ≥0) : E :=
  if h : ∃ k, stepTimes ε θ z k ≤ (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) < stepTimes ε θ z (k + 1) then
    z (stepTimes ε θ z (Nat.find h)).toNNReal
  else z t

/-- The uniform distribution on `[½, 1]`: `2 · Lebesgue` restricted to `[½, 1]`. -/
noncomputable def uniformHalfOne : Measure ℝ :=
  (2 : ℝ≥0∞) • (volume.restrict (Set.Icc (1 / 2 : ℝ) 1))

/-- The law of an i.i.d. sequence `(θ_k)_{k ≥ 0}` of random variables uniformly distributed on
`[½, 1]`: the infinite product of `uniformHalfOne`. -/
noncomputable def thetaLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => uniformHalfOne

end KurtzProtter91.Integrals


