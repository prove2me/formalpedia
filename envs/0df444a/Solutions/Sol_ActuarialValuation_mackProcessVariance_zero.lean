-- Prove2me | solution 1 for ActuarialValuation.mackProcessVariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:08:23.106232+00:00
-- url     : https://prove2.me/submissions/3b07515f-4509-4179-9532-7fcce7aa07f3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackProcessVariance
open ActuarialValuation

theorem solution(s : ℝ) : mackProcessVariance s 0 = 0 := by
  simp [mackProcessVariance]
