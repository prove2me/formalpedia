-- Prove2me | Definitions.Def_CompInvestBayes_IsOptimalThresholds
-- name    : CompInvestBayes_IsOptimalThresholds
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:09.499996+00:00
-- url     : https://prove2.me/theorems/ac2c8001-45e7-4e34-be5f-59db9f9466e1
-- title:
--   Two-threshold policy $(\ell,h)$, its value $v(\cdot;S_1)$ and optimal thresholds
-- statement:
--   For thresholds $\ell<h$ the **two-threshold policy** invests at
--
--   $$
--   \tau=\inf\{t\ge0:\pi_t\in[0,\ell]\cup[h,1]\}\qquad(\inf\emptyset=\infty)
--   $$
--
--   the size $S_2=\mu_{2,L}$ if $\pi_\tau\in[0,\ell]$ and $S_2=\mu_{2,H}$ if $\pi_\tau\in[h,1]$. Its value $v(y;S_1)$ is the follower's expected discounted profit (7) under this policy from the prior $y$.
--
--   The pair $(\ell,h)$ is a pair of **optimal thresholds** for $S_1$ if $0<\ell<h<1$ and, for every prior $y_0\in[0,1]$, the two-threshold policy is a feasible follower strategy and a best response.
--
--   **Formalization Note** The paper's $\ell^*(S_1),h^*(S_1)$ are the pair built in the proof of Proposition 1; milestones about them are stated for every pair of optimal thresholds. On $\{\tau=\infty\}$ the size is irrelevant.
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), two-threshold policy p.11; Propositions 1–2(a), pp.11–12 (PDF 11–12)

import Mathlib
import Definitions.Def_CompInvestBayes_posterior
import Definitions.Def_CompInvestBayes_FollowerStrategy

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CompInvestBayes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Investment time of the two-threshold policy** `(ℓ, h)` (SSRN 3408260, p.11, PDF 11):
`τ = inf{t ≥ 0 : π_t ∈ [0, ℓ] ∪ [h, 1]}`, with `inf ∅ = ∞` (`⊤`). -/
noncomputable def thrTau (p : Params) (σ : ℝ) (E : Setup Ω) (S1 ℓ h y0 : ℝ) (ω : Ω) :
    WithTop ℝ≥0 :=
  sInf ((fun t : ℝ≥0 => (t : WithTop ℝ≥0)) ''
    {t : ℝ≥0 | posterior p σ E S1 y0 t ω ≤ ℓ ∨ h ≤ posterior p σ E S1 y0 t ω})

/-- **Investment size of the two-threshold policy** `(ℓ, h)` (SSRN 3408260, p.11, PDF 11):
`S₂ = µ_{2,L}` if `π_τ ∈ [0, ℓ]` and `S₂ = µ_{2,H}` if `π_τ ∈ [h, 1]`.

**Formalization Note.** On `{τ = ∞}` the size is irrelevant (the follower never invests); the
formula then reads the belief at time `0`. -/
noncomputable def thrS2 (p : Params) (σ : ℝ) (E : Setup Ω) (S1 ℓ h y0 : ℝ) (ω : Ω) : ℝ :=
  if posterior p σ E S1 y0 ((thrTau p σ E S1 ℓ h y0 ω).untopD 0) ω ≤ ℓ then p.mu2L else p.mu2H

/-- **The follower's value function under the two-threshold policy** `(ℓ, h)`,
`v(y; S₁)` (SSRN 3408260, Proposition 1, p.11, PDF 11): the follower's expected total discounted
profit (7) under the policy `(thrTau, thrS2)` when the prior is `π₀ = y`. -/
noncomputable def thrValue (p : Params) (σ : ℝ) (E : Setup Ω) (S1 ℓ h y : ℝ) : ℝ :=
  followerValue p σ E y (thrTau p σ E S1 ℓ h y) (thrS2 p σ E S1 ℓ h y)

/-- **`(ℓ, h)` are optimal belief thresholds** of the follower for the leader size `S₁`
(SSRN 3408260, Propositions 1–2(a), pp.11–12, PDF 11–12): `0 < ℓ < h < 1`, and for every prior
`y₀ ∈ [0, 1]` the two-threshold policy `(thrTau, thrS2)` is a feasible follower strategy that is
optimal (attains the maximum in (9)).

**Formalization Note.** The paper's `ℓ*(S₁), h*(S₁)` are the pair constructed in the proof of
Proposition 1; statements about them are stated for every pair satisfying this predicate. -/
def IsOptimalThresholds (p : Params) (σ : ℝ) (E : Setup Ω) (S1 ℓ h : ℝ) : Prop :=
  0 < ℓ ∧ ℓ < h ∧ h < 1 ∧
    ∀ y0 ∈ Set.Icc (0 : ℝ) 1, ∃ s : FollowerStrategy p σ E S1 y0,
      s.τ = thrTau p σ E S1 ℓ h y0 ∧ s.S2 = thrS2 p σ E S1 ℓ h y0 ∧ IsFollowerOptimal s

end CompInvestBayes


