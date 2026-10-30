-- Prove2me | Definitions.Def_VehShare_SeqBounds_avail
-- name    : VehShare_SeqBounds_avail
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:42:43.749218+00:00
-- url     : https://prove2.me/theorems/73e722ba-9063-4f63-b90a-5100fd3bbb7e
-- title:
--   Availability $\alpha_i$ of a location
-- statement:
--   The **availability** of location $i$ under a distribution $\pi$ is (p. 6)
--
--   $$
--   \alpha_i=\sum_{x:\,x_i>0}\pi(x),
--   $$
--
--   the probability that a customer, upon arrival, finds a vehicle at $i$.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, p. 6

import Mathlib
import Definitions.Def_VehShare_SeqBounds_State

namespace VehShare.SeqBounds

open Classical in
/-- **Availability `α_i` of location `i`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), p. 6: "`α_i` is the probability that a customer, upon arrival, finds vehicles available at
location `i` (i.e., `α_i = ∑_{x:x_i>0} π(x)`)".

The `π`-probability of the states with at least one vehicle at `i` (Poisson arrivals see time
averages). -/
noncomputable def avail {P : Instance} {K : ℕ} (π : State P K → ℝ) (i : P.L) : ℝ :=
  ∑ z ∈ Finset.univ.filter (fun z : State P K => 1 ≤ z.1 (Sum.inl i)), π z

end VehShare.SeqBounds


