-- Prove2me | Definitions.Def_OnlinePrimalDual_BoundedAllocation_allocX
-- name    : OnlinePrimalDual_BoundedAllocation_allocX
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:04:15.786296+00:00
-- url     : https://prove2.me/theorems/90bf1e41-ded1-46ab-9648-8f3356dcb3de
-- title:
--   The algorithm's primal variable as a function of a buyer's final level
-- statement:
--   `allocX d t i := f_d(t(i)/d)`, the primal variable `x(i)` the analysis assigns to buyer `i`,
--   as the potential function evaluated at `i`'s final level `t(i)` (the highest level `i` reaches
--   during the algorithm's execution). Models only the final-state branch of the book's own
--   two-branch piecewise `x(i)` (clarified per moderation, 2026-09-21): correct because, by
--   `t(i)`'s own definition, the buyer's final spend fraction is always `≥ t(i)/d`, so the capped
--   branch is exactly the one that applies at the end of the run.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 241

import Mathlib
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_potential

namespace OnlinePrimalDual.BoundedAllocation

/-- The primal variable `x(i)` the allocation algorithm's analysis assigns to buyer `i`
(Buchbinder & Naor, FnT TCS 2009, p. 241: "the variable `x(i)` grows as a function of the
fraction of money that buyer `i` spent"), as the potential function evaluated at buyer `i`'s
final level `t i` (`0 ≤ t i ≤ d`, "the highest level `i` to which this buyer belongs during the
execution of the algorithm", p. 241). -/
noncomputable def allocX {I : Type*} (d : ℕ) (t : I → ℕ) (i : I) : ℝ :=
  potential d (t i)

end OnlinePrimalDual.BoundedAllocation


