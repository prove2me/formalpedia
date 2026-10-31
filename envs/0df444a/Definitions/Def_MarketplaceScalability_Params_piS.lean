-- Prove2me | Definitions.Def_MarketplaceScalability_Params_piS
-- name    : MarketplaceScalability_Params_piS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:51:17.558627+00:00
-- url     : https://prove2.me/theorems/56cff0c4-6f3b-4666-b92f-cd442d3a282b
-- title:
--   Scalable profit function $\pi_S$, eq. (6)
-- statement:
--   The platform's post-investment profit function in the scalable scenario: $\pi_S(p)=\pi(p)$ if sellers use the platform service at price $p$, and $\pi_S(p)=\pi_o$ otherwise.
--
--   **Formalization Note** The source writes this case distinction with the cutoff $p_s$. Here it is the sellers' comparison, and a theorem of the mission shows that the result is the source's eq. (6).
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, eq. (6), p.9

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_piO
import Definitions.Def_MarketplaceScalability_Params_pi
import Definitions.Def_MarketplaceScalability_Params_usesPlatformS

namespace MarketplaceScalability

open Classical in
/-- The platform's post-investment profit in the scalable scenario: `π(p)` if sellers use the platform
service at `p`, and `π_o` otherwise. Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, eq. (6), p.9.

**Formalization Note** The source writes the case distinction with the cutoff `p_s`; here it is the
sellers' comparison, and `piS_eq` shows that this is (6). -/
noncomputable def Params.piS (P : Params) (p : ℝ) : ℝ :=
  if P.usesPlatformS p then P.pi p else P.piO

end MarketplaceScalability


