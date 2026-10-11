-- Prove2me | solution 1 for ActuarialValuation.csJointExp_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:56:29.265187+00:00
-- url     : https://prove2.me/submissions/2bca79ec-9a0d-4d20-9943-8a6eb1bff472

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csJointExp
open ActuarialValuation

theorem solution(a b c : ℝ) : csJointExp a b c 0 0 = 1 := by
  first
  | (simp [csJointExp]; done)
  | (norm_num [csJointExp]; done)
  | (unfold csJointExp; positivity)
  | (simp only [csJointExp]; positivity)
  | (unfold csJointExp; ring)
  | (unfold csJointExp; simp; done)
  | (unfold csJointExp; norm_num; done)
  | (simp [csJointExp]; ring)
  | (unfold csJointExp; split_ifs <;> simp_all <;> linarith)
  | (unfold csJointExp; nlinarith [sq_nonneg 0])
  | (simp_all [csJointExp]; done)
  | (unfold csJointExp; simp_all; done)
  | rfl
