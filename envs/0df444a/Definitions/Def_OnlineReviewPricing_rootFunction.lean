-- Prove2me | Definitions.Def_OnlineReviewPricing_rootFunction
-- name    : OnlineReviewPricing_rootFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:52.699961+00:00
-- url     : https://prove2.me/theorems/39e294a8-064d-4487-8573-53baa32d2fbd
-- title:
--   The function $g$ of (EC.15)
-- statement:
--   The function
--
--   $$
--   g(z):=z+\exp(z)-\mu+1-\frac{\mu_0-\mu}{\gamma\ell(z)T+1}
--   $$
--
--   rewrites equation (14) as $g(z)=0$.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.15), p.ec8 (PDF 45)

import Mathlib
import Definitions.Def_OnlineReviewPricing_ell

namespace OnlineReviewPricing

/-- The function `g(z) := z + exp z - μ + 1 - (μ₀ - μ) / (γ ℓ(z) T + 1)` of (EC.15), whose zeros are
the roots of (14) (Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.15), p.ec8). -/
noncomputable def rootFunction (μ μ₀ γ T z : ℝ) : ℝ :=
  z + Real.exp z - μ + 1 - (μ₀ - μ) / (γ * ell z * T + 1)

end OnlineReviewPricing


