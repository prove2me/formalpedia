-- Prove2me | Definitions.Def_MarketplaceScalability_Params_qm
-- name    : MarketplaceScalability_Params_qm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:41.872375+00:00
-- url     : https://prove2.me/theorems/81d08f38-d8c5-4c4b-937f-baa337f4c3a4
-- title:
--   Output $q_m=q(\bar c)$ under the market service
-- statement:
--   The output of sellers who use the market service:
--   $$
--   q_m=q(\bar c).
--   $$
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §3.1, p.8

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_q

namespace MarketplaceScalability

/-- The output `q_m = q(c̄)` of sellers who use the market service. Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §3.1, p.8. -/
noncomputable def Params.qm (P : Params) : ℝ := P.q P.cbar

end MarketplaceScalability


