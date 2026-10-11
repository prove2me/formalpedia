-- Prove2me | solution 1 for ActuarialValuation.alterationPaidUpValue_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:06:07.234197+00:00
-- url     : https://prove2.me/submissions/f3fe33eb-7faa-42fd-bc88-e541f44beedd

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPaidUpValue
open ActuarialValuation

theorem solution(A : ℝ) : alterationPaidUpValue 0 A = 0 := by
  simp [alterationPaidUpValue]
