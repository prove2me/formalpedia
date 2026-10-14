-- Prove2me | solution 1 for ActuarialValuation.ulAccountPath_issue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:54:58.572989+00:00
-- url     : https://prove2.me/submissions/1d9da451-049e-4f0f-82f0-5fd52d7438f1

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAccountPath

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (initial : ℝ) (prem expenseRate flat interest mortality face : ℕ→ℝ) : ulAccountPath initial prem expenseRate flat interest mortality face 0 = initial := by
  rfl
