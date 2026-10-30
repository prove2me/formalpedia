-- Prove2me | Definitions.Def_RideHailingAV_PureHV_demandAtPrice
-- name    : RideHailingAV_PureHV_demandAtPrice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:51:11.888565+00:00
-- url     : https://prove2.me/theorems/3dd1f26e-e7ac-4797-8821-65887274030b
-- title:
--   Demand at price $d_i(p)=m_i(1-\min\{p/V,1\})$
-- statement:
--   In scenario $i$ with potential demand mass $m_i$, the demand (in ride-hours per calendar hour) at price $p$ is
--   $$d_i(p)=m_i\,(1-F(p)),\qquad F(p)=\min\{p/V,1\},$$
--   where $F$ is the rider value distribution, uniform on $[0,V]$. The revenue-maximizing price of Assumption 2 maximizes $r_i(d_i(p))$ over prices $p$.
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), eq. (2), p. 8

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market

namespace RideHailingAV.PureHV

/-- **Demand at price `p`, `d_i(p)`.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), eq. (2), p. 8:
`d_i(p) = m_i(1 − F(p))` with `F(p) = min{p/V, 1}` (values uniform on `[0, V]`). -/
noncomputable def demandAtPrice (M : Market) (m p : ℝ) : ℝ :=
  m * (1 - min (p / M.V) 1)

end RideHailingAV.PureHV


