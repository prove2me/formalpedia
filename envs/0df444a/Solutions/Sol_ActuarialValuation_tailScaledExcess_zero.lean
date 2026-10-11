-- Prove2me | solution 1 for ActuarialValuation.tailScaledExcess_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:18:21.221277+00:00
-- url     : https://prove2.me/submissions/5d3e4492-24f0-4ac1-87f3-a935eb323e0f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailScaledExcess
open ActuarialValuation

theorem solution(frac : ℝ) : tailScaledExcess 0 frac = 0 := by
  simp [tailScaledExcess]
