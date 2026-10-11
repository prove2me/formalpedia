-- Prove2me | solution 1 for ActuarialValuation.svExp_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:44:45.273928+00:00
-- url     : https://prove2.me/submissions/a45111e4-5af7-4512-83ee-5b80306b92d9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svExpSurvival
open ActuarialValuation

theorem solution(lambda : ℝ) : svExpSurvival lambda 0 = 1 := by
  first
  | (simp [svExpSurvival]; done)
  | (norm_num [svExpSurvival]; done)
  | (unfold svExpSurvival; positivity)
  | (simp only [svExpSurvival]; positivity)
  | (unfold svExpSurvival; ring)
  | (unfold svExpSurvival; simp; done)
  | (unfold svExpSurvival; norm_num; done)
  | (simp [svExpSurvival]; ring)
  | (unfold svExpSurvival; split_ifs <;> simp_all <;> linarith)
  | (unfold svExpSurvival; nlinarith [sq_nonneg 0])
  | (simp_all [svExpSurvival]; done)
  | (unfold svExpSurvival; simp_all; done)
  | rfl
