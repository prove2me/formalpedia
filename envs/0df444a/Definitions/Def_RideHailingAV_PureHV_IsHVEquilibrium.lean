-- Prove2me | Definitions.Def_RideHailingAV_PureHV_IsHVEquilibrium
-- name    : RideHailingAV_PureHV_IsHVEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:20:18.761936+00:00
-- url     : https://prove2.me/theorems/04b1dbf9-d08e-4a8f-9ab1-1483a3047ca5
-- title:
--   Pure-HV equilibrium demand (equilibrium condition (13))
-- statement:
--   In the scenario with potential demand mass $m_i$, a demand rate $d$ is a **pure-HV equilibrium** if $0\le d\le m_i$ and market revenue exactly covers the cost of the minimal fleet:
--   $$r_i(d)=w(\underline n(d))\,\underline n(d).\qquad(13)$$
--   The demand rate $d=0$ always satisfies (13); there may be several equilibria.
--
--   **Formalization Note** The range $[0,m_i]$ is the domain of the inverse demand (3).
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), eq. (13), p. 13

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_revenue
import Definitions.Def_RideHailingAV_PureHV_laborCost

namespace RideHailingAV.PureHV

/-- **Pure-HV equilibrium demand.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), eq. (13), p. 13 (equilibrium condition (13)):
`d` is an equilibrium demand rate in a scenario of potential mass `m` if `d ∈ [0, m]` and
`r_i(d) = w(n(d)) n(d)`.

**Formalization Note.** The range `[0, m]` is the domain of the inverse demand (3), p. 8. -/
def IsHVEquilibrium (M : Market) (m d : ℝ) : Prop :=
  0 ≤ d ∧ d ≤ m ∧ revenue M m d = laborCost M d

end RideHailingAV.PureHV


