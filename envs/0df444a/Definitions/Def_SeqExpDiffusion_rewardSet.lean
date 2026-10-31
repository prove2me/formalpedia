-- Prove2me | Definitions.Def_SeqExpDiffusion_rewardSet
-- name    : SeqExpDiffusion_rewardSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:03.421857+00:00
-- url     : https://prove2.me/theorems/51144568-4a98-4169-a982-c321ff7d3199
-- title:
--   Expected discounted stopping rewards $\mathbb E[e^{-r\tau}H(\tilde\delta_\tau)]$
-- statement:
--   Let $\tilde\delta$ be a belief diffusion on $(\Omega,P)$ with filtration $(\mathcal F_t)$, let $r$ be a discount rate and $H:\mathbb R\to\mathbb R$ a payoff. This is the set of expected discounted rewards
--
--   $$\Big\{\ \mathbb E\big[e^{-r\tau}H(\tilde\delta_\tau)\big]\ :\ \tau\ \text{an }(\mathcal F_t)\text{-stopping time}\ \Big\},$$
--
--   whose supremum is the value in (12).
--
--   **Formalization Note** Stopping times take values in $[0,\infty]$, and the reward on $\{\tau=\infty\}$ is $0$ (published helper `TechBreakthrough.discountedAt`). A stopping time contributes only when its reward is integrable, so no expectation takes a default value; for payoffs continuous on $[0,1]$ every stopping time qualifies.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, display (12), p.17; the set 𝕋 of stopping times, p.8

import Mathlib
import Definitions.Def_TechBreakthrough_discountedAt

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SeqExpDiffusion

/-- The set of expected discounted rewards `E[e^{−rτ} H(δ̃_τ)]` over the stopping times `τ ∈ 𝕋` of
the filtration `ℱ`, the set whose supremum is the value in (12), Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, display (12), p.17, and
`𝕋`, p.8.

**Formalization Note** Stopping times take values in `[0, ∞]` (`WithTop ℝ≥0`); on `{τ = ∞}` the
reward is `0` (`TechBreakthrough.discountedAt`), a convention (12) leaves implicit. A stopping time
contributes only when its reward is integrable, so a Bochner integral never takes its default value
`0`; for a payoff continuous on `[0, 1]` and a continuous adapted `X` in `[0, 1]` every stopping time
qualifies. -/
def rewardSet {Ω : Type*} {mΩ : MeasurableSpace Ω} (r : ℝ) (H : ℝ → ℝ) (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) : Set ℝ :=
  {y | ∃ τ : Ω → WithTop ℝ≥0, IsStoppingTime ℱ τ ∧
      Integrable (fun ω => TechBreakthrough.discountedAt r (fun t => H (X t ω)) (τ ω)) P ∧
      y = ∫ ω, TechBreakthrough.discountedAt r (fun t => H (X t ω)) (τ ω) ∂P}

end SeqExpDiffusion


