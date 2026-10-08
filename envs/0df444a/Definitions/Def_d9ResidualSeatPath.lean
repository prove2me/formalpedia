-- Prove2me | Definitions.Def_d9ResidualSeatPath
-- name    : d9ResidualSeatPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T12:38:20.43788+00:00
-- url     : https://prove2.me/theorems/1279b481-32bc-479d-a3f0-ae6bc16619bb
-- title:
--   d9ResidualSeatPath
-- statement:
--   The residual-capacity path obtained by applying the existing nested residual-seat step repeatedly over the levels above j. This is the source-decomposition definition needed to express the entering seat count for the j-th cutoff.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ResidualSeatStep
open NestedSeatAlloc.IntPolicy

/-- Residual capacity after traversing the protection levels above `j`. The outermost level is applied first, matching the nested revenue recursion. -/
noncomputable def d9ResidualSeatPath (p x : ℕ → ℝ) (j : ℕ) : ℕ → ℝ → ℝ
  | 0, s => s
  | m + 1, s => d9ResidualSeatPath p x j m (d9ResidualSeatStep p x (j + m + 1) s)


