-- Prove2me | Definitions.Def_OnlinePrimalDual_BoundedAllocation_potential
-- name    : OnlinePrimalDual_BoundedAllocation_potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:02:04.583003+00:00
-- url     : https://prove2.me/theorems/556062e8-1700-495c-88f1-2159b742e718
-- title:
--   The trade-off potential function f_d at the level grid points
-- statement:
--   `potential d j := f_d(j/d) = Σ_{t=1}^j a_t`, the piecewise-linear potential function
--   evaluated at the level grid points; `potential d 0 = 0`, `potential d d = 1`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 240

import Mathlib
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_geomSeq

namespace OnlinePrimalDual.BoundedAllocation

/-- The piecewise-linear trade-off potential function `f_d`, evaluated at the level grid points:
`f_d(j/d) := ∑_{t=1}^j a_t` (Buchbinder & Naor, FnT TCS 2009, p. 240). At `j = d` this equals `1`
(`fd(d/d) = 1`, p. 240) and `f_d(0) = 0` (empty sum). -/
noncomputable def potential (d j : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 j, geomSeq d t

end OnlinePrimalDual.BoundedAllocation


