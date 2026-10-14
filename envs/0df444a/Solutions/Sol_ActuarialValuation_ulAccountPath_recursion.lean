-- Prove2me | solution 1 for ActuarialValuation.ulAccountPath_recursion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:56:29.64817+00:00
-- url     : https://prove2.me/submissions/202150dc-42d3-4273-b958-86d72619f72a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAccountPath
import Definitions.Def_actuarial_ulTypeBNext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (initial : ℝ) (prem expenseRate flat interest mortality face : ℕ→ℝ) (n : ℕ) : ulAccountPath initial prem expenseRate flat interest mortality face (n+1) = ulTypeBNext (ulAccountPath initial prem expenseRate flat interest mortality face n) (prem n) (expenseRate n) (flat n) (interest n) (mortality n) (face n) := by
  rfl
