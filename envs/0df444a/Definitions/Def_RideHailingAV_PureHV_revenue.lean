-- Prove2me | Definitions.Def_RideHailingAV_PureHV_revenue
-- name    : RideHailingAV_PureHV_revenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:51:47.251394+00:00
-- url     : https://prove2.me/theorems/ff59cd0a-4f47-4f76-a821-ec3e213e53e6
-- title:
--   Market revenue per hour $r_i(d)=d\,p_i(d)\,t_2$
-- statement:
--   At demand rate $d$ in scenario $i$, the total market revenue per hour is
--   $$r_i(d)=d\,p_i(d)\,t_2,$$
--   since riders pay the price $p_i(d)$ per ride-hour and each ride lasts $t_2$ on average. It is the left-hand side of the equilibrium condition (13).
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), §4, p. 12 (unnumbered: $r_i(d_{HV})\equiv d_{HV}p_i(d_{HV})t_2$)

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_invDemand

namespace RideHailingAV.PureHV

/-- **Market revenue per hour `r_i(d)`.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), §4, p. 12 (unnumbered):
`r_i(d_HV) ≡ d_HV p_i(d_HV) t₂`. -/
noncomputable def revenue (M : Market) (m d : ℝ) : ℝ :=
  d * invDemand M m d * M.t2

end RideHailingAV.PureHV


