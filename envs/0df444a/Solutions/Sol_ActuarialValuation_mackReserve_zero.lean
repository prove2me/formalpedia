-- Prove2me | solution 1 for ActuarialValuation.mackReserve_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:42:57.911243+00:00
-- url     : https://prove2.me/submissions/a840b9c0-d04a-449d-abde-2c07ac945baa

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackReserve
open ActuarialValuation

theorem solution(current : ℝ) : mackReserve current current = 0 := by
  simp [mackReserve]
