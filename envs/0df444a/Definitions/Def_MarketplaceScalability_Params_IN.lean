-- Prove2me | Definitions.Def_MarketplaceScalability_Params_IN
-- name    : MarketplaceScalability_Params_IN
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:52:37.27729+00:00
-- url     : https://prove2.me/theorems/cd54c604-d449-4247-a173-6e2d014a7375
-- title:
--   Cutoff investment $I_N$
-- statement:
--   The investment level at which the platform is indifferent between offering the service and not offering it when sellers cannot scale, that is, at which (5) holds with equality:
--   $$
--   I_N=\max_{p}\pi_N(p)-\pi_m.
--   $$
--
--   **Formalization Note** The maximum over prices $p>0$ is written `sSup`; the goal theorem proves that it is attained. Prices are positive because the first-order condition has no solution at $p\le0$.
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, eq. (5), p.9; §2.5, p.7

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_piN

namespace MarketplaceScalability

/-- The cutoff investment `I_N = max_p π_N(p) − π_m` at which (5) holds with equality.
Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, eq. (5), p.9.

**Formalization Note** The maximum over prices `p > 0` is written `sSup`; `proposition_1` proves that
it is attained, so the value is not a junk value. Prices are positive because the first-order
condition has no solution at `p ≤ 0`. -/
noncomputable def Params.IN (P : Params) : ℝ := sSup (P.piN '' Set.Ioi 0) - P.piM

end MarketplaceScalability


