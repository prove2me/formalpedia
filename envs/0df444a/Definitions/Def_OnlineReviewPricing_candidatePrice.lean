-- Prove2me | Definitions.Def_OnlineReviewPricing_candidatePrice
-- name    : OnlineReviewPricing_candidatePrice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:36.81575+00:00
-- url     : https://prove2.me/theorems/4920ac90-e1f9-490a-9bb4-b08e19834e31
-- title:
--   The candidate price path $p^*(t)$ of (13)
-- statement:
--   For a constant $z$, the **candidate price path** of (13) is
--
--   $$
--   p^*(t)=1+\exp(z)+(\mu-\mu_0)\left(\frac{1}{\gamma n^*(T)+1}-\frac{1}{\gamma n^*(t)+1}\right),
--   $$
--
--   where $n^*(t)=\ell(z)t$. If $\mu_0<\mu$ the price rises over the horizon, and if $\mu_0>\mu$ it falls.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (13), p.14

import Mathlib
import Definitions.Def_OnlineReviewPricing_candidatePath

namespace OnlineReviewPricing

/-- The price path of (13):
`p*(t) = 1 + exp z + (μ - μ₀) (1 / (γ n*(T) + 1) - 1 / (γ n*(t) + 1))`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (13), p.14). -/
noncomputable def candidatePrice (μ μ₀ γ T z t : ℝ) : ℝ :=
  1 + Real.exp z +
    (μ - μ₀) * (1 / (γ * candidatePath z T + 1) - 1 / (γ * candidatePath z t + 1))

end OnlineReviewPricing


