-- Prove2me | solution 1 for ActuarialValuation.whWeightedFit_zero_weight
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:11:48.382389+00:00
-- url     : https://prove2.me/submissions/7be87fe8-02b1-492c-8610-d79062a09be9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whWeightedFit
open ActuarialValuation

theorem solution(g q : ℝ) : whWeightedFit 0 g q = 0 := by
  simp [whWeightedFit]
