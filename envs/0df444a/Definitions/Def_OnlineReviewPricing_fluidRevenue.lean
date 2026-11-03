-- Prove2me | Definitions.Def_OnlineReviewPricing_fluidRevenue
-- name    : OnlineReviewPricing_fluidRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:30.834909+00:00
-- url     : https://prove2.me/theorems/7ee092d5-5f32-4f0d-a8e2-f58d21d2cbf3
-- title:
--   Fluid revenue $\bar J^\psi_T=\int_0^T p(t)\lambda(p(t),n(t))\,dt$
-- statement:
--   The total revenue of a path $(p,n)$ over $[0,T]$ is
--
--   $$
--   \bar J^{\psi}_T=\int_0^T p(t)\,\lambda\bigl(p(t),n(t)\bigr)\,dt .
--   $$
--
--   This is the objective of the seller's fluid problem.
--
--   **Formalization Note** On an admissible pair the integrand is bounded and measurable, so the integral is a genuine one.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (9), p.12

import Mathlib
import Definitions.Def_OnlineReviewPricing_demand

namespace OnlineReviewPricing

/-- The total fluid revenue of the path `(p, n)`, `J̄ψ_T = ∫₀ᵀ p(t) λ(p(t), n(t)) dt`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (9), p.12).

**Formalization Note.** On an admissible pair the integrand is bounded and measurable, because
`demand` has values in `(0, 1)` and `p` is bounded (`IsPiecewiseContinuousOn`). So this is a genuine
integral. -/
noncomputable def fluidRevenue (μ μ₀ γ T : ℝ) (p n : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, p t * demand μ μ₀ γ (p t) (n t)

end OnlineReviewPricing


