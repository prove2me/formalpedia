-- Prove2me | Definitions.Def_MarketplaceScalability_Params_sellerProfit
-- name    : MarketplaceScalability_Params_sellerProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:15.760098+00:00
-- url     : https://prove2.me/theorems/7c2e06e2-f7cc-405d-97eb-875cd10f6f9c
-- title:
--   The seller's objective $(1-\alpha)R(x)-\tilde c x-\tilde F$
-- statement:
--   The objective of a seller who uses a service with marginal cost $\tilde c$ and fixed fee $\tilde F$, at output $x$:
--   $$
--   (1-\alpha)R(x)-\tilde c\,x-\tilde F.
--   $$
--   The sellers' marginal cost of production is normalized to zero.
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §2.4, p.6

import Mathlib
import Definitions.Def_MarketplaceScalability_Params

namespace MarketplaceScalability

/-- The seller's objective `(1 − α) R(x) − c̃ x − F̃` at output `x`, for a service with marginal cost
`c̃` and fixed fee `F̃`. Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §2.4, p.6. -/
def Params.sellerProfit (P : Params) (ct Ft x : ℝ) : ℝ :=
  (1 - P.α) * P.R x - ct * x - Ft

end MarketplaceScalability


