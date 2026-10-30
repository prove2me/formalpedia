-- Prove2me | Definitions.Def_RideHailingAV_PureHV_wage
-- name    : RideHailingAV_PureHV_wage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:52:20.015334+00:00
-- url     : https://prove2.me/theorems/2a8682da-e5b5-4116-aacf-2a22a6eaced9
-- title:
--   HV reservation earnings $w(n)=w_0+\alpha n$
-- statement:
--   The HV supply curve: for a fleet of $n$ human drivers to participate, their hourly earnings must equal the reservation earnings
--   $$w(n)=w_0+\alpha n,\qquad \alpha\ge0.$$
--   A smaller $\alpha$ means a more elastic HV supply; $\alpha=0$ is perfectly elastic supply at earnings $w_0$.
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), eq. (1), p. 7

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market

namespace RideHailingAV.PureHV

/-- **HV reservation earnings `w(n_HV)`.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), eq. (1), p. 7:
`w(n_HV) = w₀ + α n_HV`. -/
def wage (M : Market) (n : ℝ) : ℝ :=
  M.w0 + M.α * n

end RideHailingAV.PureHV


