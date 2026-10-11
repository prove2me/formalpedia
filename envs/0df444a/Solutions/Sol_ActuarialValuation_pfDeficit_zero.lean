-- Prove2me | solution 1 for ActuarialValuation.pfDeficit_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:45:50.579854+00:00
-- url     : https://prove2.me/submissions/dbfa1a8e-f89a-4313-a79a-69cb7a298628

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfDeficit
open ActuarialValuation

theorem solution(a : ℝ) : pfDeficit a a=0 := by
  first
  | (simp [pfDeficit]; done)
  | (norm_num [pfDeficit]; done)
  | (unfold pfDeficit; positivity)
  | (simp only [pfDeficit]; positivity)
  | (unfold pfDeficit; ring)
  | (unfold pfDeficit; simp; done)
  | (unfold pfDeficit; norm_num; done)
  | (simp [pfDeficit]; ring)
  | (unfold pfDeficit; split_ifs <;> simp_all <;> linarith)
  | (unfold pfDeficit; nlinarith [sq_nonneg 0])
  | rfl
