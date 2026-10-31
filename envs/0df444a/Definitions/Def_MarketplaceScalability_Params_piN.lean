-- Prove2me | Definitions.Def_MarketplaceScalability_Params_piN
-- name    : MarketplaceScalability_Params_piN
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:51:40.701983+00:00
-- url     : https://prove2.me/theorems/b2e8a2cf-a054-4ba6-afbd-0715ca4041ac
-- title:
--   Non-scalable profit function $\pi_N$, eq. (4)
-- statement:
--   The platform's ex-post profit function in the non-scalable scenario:
--   $$
--   \pi_N(p)=\begin{cases}\pi_m,&p>\bar c,\\ \pi(p),&p\le\bar c.\end{cases}
--   $$
--   Sellers use the platform service exactly when its price does not exceed the market price.
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, eq. (4), p.8

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_piM
import Definitions.Def_MarketplaceScalability_Params_pi

namespace MarketplaceScalability

/-- The platform's ex-post profit in the non-scalable scenario: `π_N(p) = π(p)` if `p ≤ c̄`, and
`π_N(p) = π_m` if `p > c̄`. Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, eq. (4), p.8. -/
noncomputable def Params.piN (P : Params) (p : ℝ) : ℝ :=
  if p ≤ P.cbar then P.pi p else P.piM

end MarketplaceScalability


