-- Prove2me | solution 1 for ActuarialValuation.ruExponential_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:23:18.272433+00:00
-- url     : https://prove2.me/submissions/0dbd118f-c0fa-4a67-bfcf-a53882116060

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruExponential
open ActuarialValuation

theorem solution(R : ℝ) : ruExponential R 0 = 1 := by
  first
  | (simp [ruExponential]; done)
  | (norm_num [ruExponential]; done)
  | (unfold ruExponential; positivity)
  | (simp only [ruExponential]; positivity)
  | (unfold ruExponential; ring)
  | (unfold ruExponential; simp; done)
  | (unfold ruExponential; norm_num; done)
  | (simp [ruExponential]; ring)
  | (unfold ruExponential; split_ifs <;> simp_all <;> linarith)
  | (unfold ruExponential; nlinarith [sq_nonneg 0])
  | (simp_all [ruExponential]; done)
  | (unfold ruExponential; simp_all; done)
  | rfl
