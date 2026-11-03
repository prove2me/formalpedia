-- Prove2me | Definitions.Def_OnlineReviewPricing_postMean
-- name    : OnlineReviewPricing_postMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:38.301129+00:00
-- url     : https://prove2.me/theorems/3a4c5d38-f79f-45e6-89e6-7f43ededf669
-- title:
--   The posterior mean $\mu(n)$ after $n$ reviews, formula (2) with $\bar q=\mu$
-- statement:
--   Let $\mu$ be the true mean quality of the product, $\mu_0$ the mean of the customers' common prior and $\gamma=\sigma_0^2/\sigma^2>0$ the learning rate. In the fluid model the average rating equals $\mu$, so after $n$ reviews the posterior mean is
--
--   $$
--   \mu(n)=\frac{1}{\gamma n+1}\,\mu_0+\frac{\gamma n}{\gamma n+1}\,\mu .
--   $$
--
--   It starts at the prior mean $\mu_0$ and moves to the true mean $\mu$ as reviews accumulate. This is the only channel through which reviews affect demand.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (2), p.7, with q̄(t) = µ from §3.1, p.12

import Mathlib

namespace OnlineReviewPricing

/-- The posterior mean after `n` reviews whose average rating equals the true mean `μ`:
`μ(n) = (1 / (γ n + 1)) μ₀ + (γ n / (γ n + 1)) μ`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (2), p.7, with `q̄(t) = μ` from (10), p.12).

**Formalization Note.** `μ` is the true mean quality, `μ₀` the prior mean and `γ = σ₀²/σ²` the
learning rate. The formula is the page's. Along a fluid path `n ≥ 0`, so with `γ > 0` no division
by zero occurs. -/
noncomputable def postMean (μ μ₀ γ n : ℝ) : ℝ :=
  1 / (γ * n + 1) * μ₀ + γ * n / (γ * n + 1) * μ

end OnlineReviewPricing


