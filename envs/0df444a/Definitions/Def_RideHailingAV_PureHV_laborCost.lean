-- Prove2me | Definitions.Def_RideHailingAV_PureHV_laborCost
-- name    : RideHailingAV_PureHV_laborCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:53:55.296841+00:00
-- url     : https://prove2.me/theorems/cf45515c-3c0d-42a0-b866-b7af2948e4d2
-- title:
--   Total HV labor cost $w(\underline n(d))\,\underline n(d)$
-- statement:
--   At demand rate $d$, the minimal fleet $\underline n(d)$ must be paid its reservation earnings, so the total labor cost per hour is
--   $$C(d)=w(\underline n(d))\,\underline n(d).$$
--   It is the right-hand side of the equilibrium condition (13), $r_i(d)=w(\underline n(d))\underline n(d)$.
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), eq. (13), p. 13

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_wage
import Definitions.Def_RideHailingAV_PureHV_minSupply

namespace RideHailingAV.PureHV

/-- **Total labor cost `w(n(d)) n(d)`.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), eq. (13), p. 13: the right-hand side of the
equilibrium condition `r_i(d_HV) = w(n(d_HV)) n(d_HV)`. -/
noncomputable def laborCost (M : Market) (d : ℝ) : ℝ :=
  wage M (minSupply M d) * minSupply M d

end RideHailingAV.PureHV


