-- Prove2me | Definitions.Def_OnlinePrimalDual_BoundedAllocation_geomSeq
-- name    : OnlinePrimalDual_BoundedAllocation_geomSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:01:21.118794+00:00
-- url     : https://prove2.me/theorems/89e21330-2ab9-4447-87b7-991c1c18e955
-- title:
--   The geometric sequence underlying the trade-off potential function
-- statement:
--   `geomSeq d t := a_t`, the geometric sequence `a_1 = (1/d)((1+1/(d-1))^(d-1) - (d-1))`,
--   `a_t = a_1(1+1/(d-1))^(t-1)`, combined into a single closed form.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 239-240

import Mathlib

namespace OnlinePrimalDual.BoundedAllocation

/-- The geometric sequence `aₜ` (`1 ≤ t ≤ d`) underlying the trade-off potential function `f_d`
(Buchbinder & Naor, FnT TCS 2009, p. 239-240): `a₁ = (1/d)((1+1/(d-1))^(d-1) - (d-1))`,
`aₜ = a₁(1+1/(d-1))^(t-1)`. Combined here into a single closed form. -/
noncomputable def geomSeq (d t : ℕ) : ℝ :=
  (1 / (d : ℝ)) * ((1 + 1 / ((d : ℝ) - 1)) ^ (d - 1) - ((d : ℝ) - 1)) *
    (1 + 1 / ((d : ℝ) - 1)) ^ (t - 1)

end OnlinePrimalDual.BoundedAllocation


