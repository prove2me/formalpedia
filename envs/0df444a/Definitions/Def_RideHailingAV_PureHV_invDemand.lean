-- Prove2me | Definitions.Def_RideHailingAV_PureHV_invDemand
-- name    : RideHailingAV_PureHV_invDemand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:50:37.707872+00:00
-- url     : https://prove2.me/theorems/4e0133c5-626d-4edd-b06b-d9adec882dad
-- title:
--   Inverse demand $p_i(d)=V(1-d/m_i)$
-- statement:
--   In a demand scenario with potential demand mass $m_i>0$ and rider values uniform on $[0,V]$, the price at which the demand rate is $d$ is
--   $$p_i(d)=V\Big(1-\frac{d}{m_i}\Big),\qquad d\in[0,m_i].$$
--   This is the inverse of the demand function $d_i(p)=m_i(1-\min\{p/V,1\})$; it gives the market-clearing price of a demand rate.
--
--   **Formalization Note** The function is defined for every real $d$; all statements of the mission apply it to $d\in[0,m_i]$ with $m_i>0$.
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), eq. (3), p. 8

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market

namespace RideHailingAV.PureHV

/-- **Inverse demand `p_i(d)`.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), eq. (3), p. 8:
`p_i(d) = V(1 − d/m_i)`, `d ∈ [0, m_i]`, for a scenario of potential demand mass `m = m_i`.

**Formalization Note.** Defined for every real `d`; every theorem of the mission applies it to
`d ∈ [0, m]` with `0 < m`. -/
noncomputable def invDemand (M : Market) (m d : ℝ) : ℝ :=
  M.V * (1 - d / m)

end RideHailingAV.PureHV


