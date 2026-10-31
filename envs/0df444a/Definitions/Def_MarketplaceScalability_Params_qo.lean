-- Prove2me | Definitions.Def_MarketplaceScalability_Params_qo
-- name    : MarketplaceScalability_Params_qo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:26.624705+00:00
-- url     : https://prove2.me/theorems/f209c360-360a-494a-914b-17a63934fd7f
-- title:
--   Output $q_o=q(\underline c)$ under own service
-- statement:
--   The output of sellers who use their own service:
--   $$
--   q_o=q(\underline c).
--   $$
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §3.1, p.9

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_q

namespace MarketplaceScalability

/-- The output `q_o = q(c̲)` of sellers who use their own service. Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §3.1, p.9. -/
noncomputable def Params.qo (P : Params) : ℝ := P.q P.cown

end MarketplaceScalability


