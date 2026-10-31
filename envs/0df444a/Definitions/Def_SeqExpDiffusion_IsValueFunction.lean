-- Prove2me | Definitions.Def_SeqExpDiffusion_IsValueFunction
-- name    : SeqExpDiffusion_IsValueFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:48.934682+00:00
-- url     : https://prove2.me/theorems/9cfd2797-add1-41e0-958e-f396cd94448f
-- title:
--   The value function $\tilde{\mathcal G}(\delta)=\sup_\tau\mathbb E_\delta[e^{-r\tau}H(\tilde\delta_\tau)]$ of (12)
-- statement:
--   Let $r$ be a discount rate, $\tilde\sigma$ a volatility and $H$ a payoff. A function $v$ is **the value function** of the optimal stopping problem
--
--   $$\tilde{\mathcal G}(\delta):=\sup_{\tau\in\mathbb T}\mathbb E_\delta\big[e^{-r\tau}H(\tilde\delta_\tau)\big]\quad\text{subject to}\quad d\tilde\delta_t=\tilde\sigma\,\tilde\delta_t(1-\tilde\delta_t)\,dW_t,\ \ \tilde\delta_0=\delta,$$
--
--   if for every $\delta\in[0,1]$ and every belief diffusion $\tilde\delta$ started at $\delta$ (on any probability space, with any filtration for which $W$ is Brownian), $v(\delta)$ is the least upper bound of the expected discounted rewards over the stopping times.
--
--   With $H=G$ this is the paper's $\tilde{\mathcal G}$; with $H=\tilde G_{ij}$ it is the value $\tilde{\mathcal G}_{ij}$ of the two-action problem.
--
--   **Formalization Note** The supremum is expressed as a least upper bound, so it is never a default value. Requiring the same $v(\delta)$ for every solution is what makes "the" value well defined; $v$ is constrained on $[0,1]$ only. Rewards at $\tau=\infty$ are $0$.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, display (12), p.17

import Mathlib
import Definitions.Def_SeqExpDiffusion_IsBeliefDiffusion
import Definitions.Def_SeqExpDiffusion_rewardSet

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SeqExpDiffusion

/-- `v` is the value function `𝒢̃` of the optimal stopping problem (12) with discount rate `r`,
volatility `σ̃ = σ` and payoff `H`:
`𝒢̃(δ) = sup_{τ ∈ 𝕋} E_δ[e^{−rτ} H(δ̃_τ)]`, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, display (12), p.17.

For every `δ ∈ [0, 1]` and every belief diffusion `X` started at `δ` (on any probability space, with
any filtration for which the driving motion is Brownian), `v δ` is the least upper bound of the
expected rewards over the stopping times.

**Formalization Note** The value is stated with `IsLUB`, not with a real `sSup` (whose value on an
unbounded set is `0`). Requiring the same `v δ` for every solution of (12) is what makes "the" value
well defined; `v` is constrained on `[0, 1]` only. -/
def IsValueFunction (r σ : ℝ) (H v : ℝ → ℝ) : Prop :=
  ∀ δ ∈ Set.Icc (0 : ℝ) 1, ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ) (B X : ℝ≥0 → Ω → ℝ),
    IsBeliefDiffusion σ δ P ℱ B X → IsLUB (rewardSet r H P ℱ X) (v δ)

end SeqExpDiffusion


