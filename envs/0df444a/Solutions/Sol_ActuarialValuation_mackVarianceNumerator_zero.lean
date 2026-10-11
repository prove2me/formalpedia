-- Prove2me | solution 1 for ActuarialValuation.mackVarianceNumerator_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:20:58.557722+00:00
-- url     : https://prove2.me/submissions/aaad68aa-a44d-4080-a209-7bd0a3bd3680

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackVarianceNumerator
open ActuarialValuation

theorem solution(a b e : ℕ → ℝ) : mackVarianceNumerator a b e 0 = 0 := by
  simp [mackVarianceNumerator]
