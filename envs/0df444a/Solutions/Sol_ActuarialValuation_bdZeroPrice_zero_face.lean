-- Prove2me | solution 1 for ActuarialValuation.bdZeroPrice_zero_face
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:50:56.499479+00:00
-- url     : https://prove2.me/submissions/92eb9367-c0ca-44bf-bd30-a77a48a84a92

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdZeroPrice
open ActuarialValuation

theorem solution(D : ℕ → ℝ) (t : ℕ) : bdZeroPrice D 0 t = 0 := by
  simp [bdZeroPrice]
