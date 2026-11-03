-- Prove2me | Definitions.Def_OnlineReviewPricing_IsRootOf14
-- name    : OnlineReviewPricing_IsRootOf14
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:52.30705+00:00
-- url     : https://prove2.me/theorems/81a763ad-847a-48d2-83e5-b40713f7db1e
-- title:
--   Equation (14) for the constant $z^*$
-- statement:
--   A real number $z$ is a **root of (14)** if
--
--   $$
--   z+\exp(z)=\mu-1+\frac{\mu_0-\mu}{\gamma\,\ell(z)\,T+1}.
--   $$
--
--   Each root gives a candidate price path through (13). Equation (14) can have several roots when condition (15) fails.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (14), p.14

import Mathlib
import Definitions.Def_OnlineReviewPricing_ell

namespace OnlineReviewPricing

/-- `z` solves equation (14): `z + exp z = μ - 1 + (μ₀ - μ) / (γ ℓ(z) T + 1)`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (14), p.14). -/
def IsRootOf14 (μ μ₀ γ T z : ℝ) : Prop :=
  z + Real.exp z = μ - 1 + (μ₀ - μ) / (γ * ell z * T + 1)

end OnlineReviewPricing


