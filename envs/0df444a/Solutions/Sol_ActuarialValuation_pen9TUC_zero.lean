-- Prove2me | solution 1 for ActuarialValuation.pen9TUC_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:29:17.739606+00:00
-- url     : https://prove2.me/submissions/ddd51ecf-ee35-4a47-a17f-b0699f3af4f1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9TUC
open ActuarialValuation

theorem solution(a current f : ℝ) : pen9TUC a current f 0 = 0 := by
  simp [pen9TUC]
