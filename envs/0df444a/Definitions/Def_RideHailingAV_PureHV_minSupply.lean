-- Prove2me | Definitions.Def_RideHailingAV_PureHV_minSupply
-- name    : RideHailingAV_PureHV_minSupply
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:52:51.046138+00:00
-- url     : https://prove2.me/theorems/23ea4507-d46e-47ec-a7a5-e5fc2538548d
-- title:
--   Minimal supply $\underline n(d)=\min_s\{s+d(t_1(s)+t_2)\}$
-- statement:
--   To serve a demand rate $d$, by Little's law $d\,(t_1(s)+t_2)$ cars are busy picking up or on a trip when $s$ cars are open, so a fleet of $s+d(t_1(s)+t_2)$ cars is needed. The **minimal supply** for demand $d$ is
--   $$\underline n(d)=\min_{s}\{\,s+d\,(t_1(s)+t_2)\,\},\qquad t_1(s)=a s^{-r}.$$
--   It is the fleet size in a competitive equilibrium with demand $d$ (eq. (12)).
--
--   **Formalization Note** The minimum over the number of open cars is formalized as the infimum over $s>0$. Lemma 1 (a milestone of this mission) shows the value is $\tilde a d^{1/(r+1)}+t_2 d$. At $r>0$ the point $s=0$ is excluded because $t_1(0)$ is undefined; at $r=0$ the paper's minimizer is $s=0$, and the infimum over $s>0$ has the same value. For $d\ge0$ the set is nonempty and bounded below by $0$; the mission applies $\underline n$ only to $d\ge 0$.
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), §4, p. 12 (unnumbered display) and eq. (23), p. 38

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market

namespace RideHailingAV.PureHV

/-- **Minimal supply `n(d)`.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), §4, p. 12 and eq. (23), p. 38:
`n(d_HV) = min_s {s + d_HV (t₁(s) + t₂)}` with `t₁(s) = a s^(−r)`.

**Formalization Note.** The minimum over the number `s` of open cars is the infimum over
`s > 0`. The values agree (Lemma 1 computes the minimum in closed form, see
`lemma_1_min_supply_closed_form`). At `r = 0` the paper's minimizer is `s = 0`
(`t₁ ≡ a`), which the open domain does not contain but approaches; at `r > 0` the point
`s = 0` is excluded because `t₁(0)` is undefined (Lean's `0 ^ (−r) = 0` would be a junk value).
For `d ≥ 0` the set is nonempty and bounded below by `0`, so the infimum is the true one; the
mission only applies `minSupply` to `d ≥ 0`. -/
noncomputable def minSupply (M : Market) (d : ℝ) : ℝ :=
  sInf ((fun s : ℝ => s + d * (M.a * s ^ (-M.r) + M.t2)) '' Set.Ioi 0)

end RideHailingAV.PureHV


