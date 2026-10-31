-- Prove2me | Definitions.Def_MarketplaceScalability_Params_piO
-- name    : MarketplaceScalability_Params_piO
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:50:14.703113+00:00
-- url     : https://prove2.me/theorems/63bb68c2-ed10-4042-8907-417dfd0e4290
-- title:
--   Platform profit $\pi_o=\alpha R(q_o)$
-- statement:
--   The platform's profit when sellers use their own service:
--   $$
--   \pi_o=\alpha R(q_o).
--   $$
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §3.1, p.9

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_qo

namespace MarketplaceScalability

/-- The platform's profit `π_o = α R(q_o)` when sellers use their own service.
Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §3.1, p.9. -/
noncomputable def Params.piO (P : Params) : ℝ := P.α * P.R P.qo

end MarketplaceScalability


