-- Prove2me | Definitions.Def_MarketplaceScalability_Params_piM
-- name    : MarketplaceScalability_Params_piM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:53.165217+00:00
-- url     : https://prove2.me/theorems/4d2d58dd-5005-486f-ac15-74671ee9bf2c
-- title:
--   Platform profit $\pi_m=\alpha R(q_m)$
-- statement:
--   The platform's profit when sellers use the market service:
--   $$
--   \pi_m=\alpha R(q_m).
--   $$
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §3.1, p.8

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_qm

namespace MarketplaceScalability

/-- The platform's profit `π_m = α R(q_m)` when sellers use the market service.
Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §3.1, p.8. -/
noncomputable def Params.piM (P : Params) : ℝ := P.α * P.R P.qm

end MarketplaceScalability


