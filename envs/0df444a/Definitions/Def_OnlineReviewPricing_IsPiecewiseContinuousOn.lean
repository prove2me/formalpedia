-- Prove2me | Definitions.Def_OnlineReviewPricing_IsPiecewiseContinuousOn
-- name    : OnlineReviewPricing_IsPiecewiseContinuousOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:36.785234+00:00
-- url     : https://prove2.me/theorems/1e4dff41-b426-44bb-a70c-c36bed7c4fd4
-- title:
--   Piecewise continuous paths on $[0,T]$
-- statement:
--   A function $p:[0,T]\to\mathbb R$ is **piecewise continuous** if there is a finite set $A\subseteq[0,T]$ such that $p$ is continuous at every point of $[0,T]\setminus A$, and $p$ has a finite right limit at every $t\in[0,T)$ and a finite left limit at every $t\in(0,T]$.
--
--   These are the price paths $\Psi$ over which the seller optimizes. Prices are real numbers and may be negative: the constraint $p(t)\in[\underline p,\bar p]$ of the stochastic model is dropped in the fluid problem (§3.1, p.12).
--
--   **Formalization Note** The paper does not spell out "piecewise continuous". The finite one-sided limits are the usual meaning and they make $p$ bounded. Without them, $p(t)=-1/t$ would be admissible and its revenue integral would not exist.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), §3.1, p.12 (the class Ψ of piecewise continuous paths)

import Mathlib

open Filter Topology

namespace OnlineReviewPricing

/-- `p` is a piecewise continuous path on `[0, T]`: it is continuous on `[0, T]` off a finite
subset, and has finite one-sided limits at every point of `[0, T]`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), §3.1, p.12, the class `Ψ`).

**Formalization Note.** The page says "piecewise continuous" with no further detail. The finite
one-sided limits are the standard meaning. They make `p` bounded, so that the integrals of the
fluid model are genuine. Only the values of `p` on `[0, T]` matter. Prices are real and may be
negative. -/
def IsPiecewiseContinuousOn (T : ℝ) (p : ℝ → ℝ) : Prop :=
  ∃ A : Finset ℝ, (↑A : Set ℝ) ⊆ Set.Icc 0 T ∧
    (∀ t ∈ Set.Icc 0 T, t ∉ A → ContinuousWithinAt p (Set.Icc 0 T) t) ∧
    (∀ t ∈ Set.Ico 0 T, ∃ l : ℝ, Tendsto p (𝓝[>] t) (𝓝 l)) ∧
    (∀ t ∈ Set.Ioc 0 T, ∃ l : ℝ, Tendsto p (𝓝[<] t) (𝓝 l))

end OnlineReviewPricing


