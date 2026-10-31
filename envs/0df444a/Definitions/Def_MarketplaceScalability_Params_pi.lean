-- Prove2me | Definitions.Def_MarketplaceScalability_Params_pi
-- name    : MarketplaceScalability_Params_pi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:41.604923+00:00
-- url     : https://prove2.me/theorems/91f0e8ad-8ef8-4c49-82b4-3bdcc4973c4f
-- title:
--   Platform profit $\pi(p)=\alpha R(q(p))+(p-c)q(p)$, eq. (3)
-- statement:
--   The platform's ex-post profit when it offers the service at price $p$ and sellers use it:
--   $$
--   \pi(p)=\alpha R(q(p))+(p-c)\,q(p).
--   $$
--   The first term is the commission and the second is the margin on the service. The investment $I$ is not subtracted.
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, eq. (3), p.8

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_q

namespace MarketplaceScalability

/-- The platform's ex-post profit `π(p) = α R(q(p)) + (p − c) q(p)` when sellers use the platform
service at price `p`. Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, eq. (3), p.8. -/
noncomputable def Params.pi (P : Params) (p : ℝ) : ℝ :=
  P.α * P.R (P.q p) + (p - P.c) * P.q p

end MarketplaceScalability


