-- Prove2me | Definitions.Def_MarketplaceScalability_Params_sellerPayoff
-- name    : MarketplaceScalability_Params_sellerPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:39.87608+00:00
-- url     : https://prove2.me/theorems/b7d734bd-2663-4fb5-bba4-4de10e5d27d8
-- title:
--   The seller's payoff at a service $(\tilde c,\tilde F)$
-- statement:
--   The value of the seller's problem at the service $(\tilde c,\tilde F)$:
--   $$
--   (1-\alpha)R(q(\tilde c))-\tilde c\,q(\tilde c)-\tilde F.
--   $$
--   These are the expressions compared in Assumption 1 and in the definition of the cutoff price. That $q(\tilde c)$ maximizes the seller's objective is a theorem of the mission.
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §2.4, p.6; eq. (1), p.6

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_q
import Definitions.Def_MarketplaceScalability_Params_sellerProfit

namespace MarketplaceScalability

/-- The value `(1 − α) R(q(c̃)) − c̃ q(c̃) − F̃` of the seller's problem at service `(c̃, F̃)`.
Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §2.4, p.6, and the two sides of (1).

The theorem `foc_output` shows that `q c̃` maximizes the objective. -/
noncomputable def Params.sellerPayoff (P : Params) (ct Ft : ℝ) : ℝ :=
  P.sellerProfit ct Ft (P.q ct)

end MarketplaceScalability


