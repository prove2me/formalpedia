-- Prove2me | Definitions.Def_OnlineReviewPricing_IsCriticalRoot
-- name    : OnlineReviewPricing_IsCriticalRoot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:01.256088+00:00
-- url     : https://prove2.me/theorems/0003cce9-37be-488c-ab41-e50b665db4e8
-- title:
--   The limit equation of (14) as $\gamma T\to\kappa$
-- statement:
--   A real number $z$ is a **root of the limit equation** at $\kappa>0$ if
--
--   $$
--   z+\exp(z)=\mu-1+\frac{\mu_0-\mu}{\kappa\,\ell(z)+1}.
--   $$
--
--   This is equation (14) with $\gamma T$ replaced by its limit $\kappa$. It depends on $\gamma$ and $T$ only through $\kappa$.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.ec13 (PDF 50), the display before (EC.26)

import Mathlib
import Definitions.Def_OnlineReviewPricing_ell

namespace OnlineReviewPricing

/-- `z` solves `z + exp z = μ - 1 + (μ₀ - μ) / (κ ℓ(z) + 1)`, the form of (14) as `γT → κ`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.ec13). -/
def IsCriticalRoot (μ μ₀ κ z : ℝ) : Prop :=
  z + Real.exp z = μ - 1 + (μ₀ - μ) / (κ * ell z + 1)

end OnlineReviewPricing


