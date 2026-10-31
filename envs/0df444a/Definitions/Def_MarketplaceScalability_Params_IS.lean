-- Prove2me | Definitions.Def_MarketplaceScalability_Params_IS
-- name    : MarketplaceScalability_Params_IS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:52:10.252068+00:00
-- url     : https://prove2.me/theorems/f8e2a4fb-1339-4b22-aa58-e15b28179947
-- title:
--   Cutoff investment $I_S$
-- statement:
--   The investment level at which the platform is indifferent between offering the service and not offering it when sellers can scale, that is, at which (7) holds with equality:
--   $$
--   I_S=\max_{p}\pi_S(p)-\pi_o.
--   $$
--
--   **Formalization Note** The maximum over prices $p>0$ is written `sSup`; the goal theorem proves that it is attained.
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, eq. (7), p.10; §2.5, p.7

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_piS

namespace MarketplaceScalability

/-- The cutoff investment `I_S = max_p π_S(p) − π_o` at which (7) holds with equality.
Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, eq. (7), p.10.

**Formalization Note** As for `Params.IN`: the maximum over prices `p > 0` is written `sSup`, and
`proposition_1` proves that it is attained. -/
noncomputable def Params.IS (P : Params) : ℝ := sSup (P.piS '' Set.Ioi 0) - P.piO

end MarketplaceScalability


