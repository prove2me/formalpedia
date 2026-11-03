-- Prove2me | Definitions.Def_OnlineReviewPricing_scaledFixedPriceEquation
-- name    : OnlineReviewPricing_scaledFixedPriceEquation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:43.438886+00:00
-- url     : https://prove2.me/theorems/0aa8b24a-5fda-435a-ae10-7bf5a307d869
-- title:
--   The scaled equation for sales at a fixed price
-- statement:
--   With $\tilde n=\gamma n$ and $\kappa=\gamma T$, the sales equation becomes
--
--   $$
--   \tilde n-\kappa+\exp(p-\mu)\int_0^{\tilde n}\exp\left(\frac{\mu-\mu_0}{1+x}\right)dx=0 .
--   $$
--
--   It does not involve $\gamma$ and $T$ separately. This item is the left side, as a function of $\tilde n\ge 0$.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.ec14 (PDF 51), the second display

import Mathlib

namespace OnlineReviewPricing

/-- The left side of `x - κ + exp(p - μ) ∫₀ˣ exp((μ - μ₀) / (1 + y)) dy = 0`, the scaled equation
for `x = γ n` (Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.ec14). -/
noncomputable def scaledFixedPriceEquation (μ μ₀ κ p x : ℝ) : ℝ :=
  x - κ + Real.exp (p - μ) * ∫ y in (0 : ℝ)..x, Real.exp ((μ - μ₀) / (1 + y))

end OnlineReviewPricing


