-- Prove2me | Definitions.Def_D1Bound5_FrontierTableNumeric_Definitions
-- name    : D1Bound5_FrontierTableNumeric_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:00:55.576425+00:00
-- url     : https://prove2.me/theorems/ba80edd0-27c8-40ef-bf7d-57ef9c9824b0
-- title:
--   Frontier Table Numeric
-- statement:
--   The five rational parameter rows of the manuscript frontier table. The named objects in this bundle include `FrontierTableRow`.
-- source:
--   D1Bound5/FrontierTableNumeric.lean, lines 5-11, SHA-256 fdb5110fd7c01a02f52f2b7aca40f48eff76285798bc764522ee4ed8858163e4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- The five rational parameter rows of the manuscript frontier table. -/
def FrontierTableRow (alpha beta target : ℝ) : Prop :=
  (alpha = 1 ∧ beta = 8 ∧ target = 27/8) ∨
  (alpha = 140/99 ∧ beta = 4 ∧ target = 3) ∨
  (alpha = 12/7 ∧ beta = 3 ∧ target = 11/4) ∨
  (alpha = 2 ∧ beta = 3 ∧ target = 29/10) ∨
  (alpha = 20/9 ∧ beta = 3 ∧ target = 3)





end D1Bound5
end


