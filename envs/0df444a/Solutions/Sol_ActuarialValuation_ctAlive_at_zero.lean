-- Prove2me | solution 1 for ActuarialValuation.ctAlive_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:50:21.913849+00:00
-- url     : https://prove2.me/submissions/f27593b7-29ae-44f6-8617-dad19f110854

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctAlive
open ActuarialValuation

theorem solution(mu : ℝ) : ctAlive mu 0 = 1 := by
  first
  | (simp [ctAlive]; done)
  | (norm_num [ctAlive]; done)
  | (unfold ctAlive; positivity)
  | (simp only [ctAlive]; positivity)
  | (unfold ctAlive; ring)
  | (unfold ctAlive; simp; done)
  | (unfold ctAlive; norm_num; done)
  | (simp [ctAlive]; ring)
  | (unfold ctAlive; split_ifs <;> simp_all <;> linarith)
  | (unfold ctAlive; nlinarith [sq_nonneg 0])
  | rfl
