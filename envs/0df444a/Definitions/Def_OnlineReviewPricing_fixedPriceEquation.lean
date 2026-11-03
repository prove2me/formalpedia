-- Prove2me | Definitions.Def_OnlineReviewPricing_fixedPriceEquation
-- name    : OnlineReviewPricing_fixedPriceEquation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:40.889442+00:00
-- url     : https://prove2.me/theorems/d0073e3d-1946-4f70-9c53-7828a8ebcb4d
-- title:
--   The equation for total sales at a fixed price
-- statement:
--   For a fixed price $p$, the total sales $n$ over $[0,T]$ solve
--
--   $$
--   n-T+\exp(p-\mu)\int_0^n\exp\left(\frac{\mu-\mu_0}{1+\gamma x}\right)dx=0 .
--   $$
--
--   This item is the left side of that equation, as a function of $n\ge 0$.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.ec14 (PDF 51), the display after (EC.27)

import Mathlib

namespace OnlineReviewPricing

/-- The left side of `n - T + exp(p - μ) ∫₀ⁿ exp((μ - μ₀) / (1 + γ x)) dx = 0`, the equation for the
total sales at a fixed price `p` (Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.ec14).

**Formalization Note.** The equation is applied at `n ≥ 0`, where the integrand is continuous on
the range of integration. -/
noncomputable def fixedPriceEquation (μ μ₀ γ T p n : ℝ) : ℝ :=
  n - T + Real.exp (p - μ) * ∫ x in (0 : ℝ)..n, Real.exp ((μ - μ₀) / (1 + γ * x))

end OnlineReviewPricing


