-- Prove2me | solution 1 for ActuarialValuation.ruCededTotal_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:23:55.618951+00:00
-- url     : https://prove2.me/submissions/4466d270-c708-41e3-a38b-a2ede881daf8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruCededTotal
open ActuarialValuation

theorem solution(x : ℕ → ℝ) (d : ℝ) : ruCededTotal x d 0 = 0 := by
  simp [ruCededTotal]
