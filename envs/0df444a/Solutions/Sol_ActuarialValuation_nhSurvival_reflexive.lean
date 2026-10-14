-- Prove2me | solution 1 for ActuarialValuation.nhSurvival_reflexive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:36:21.950414+00:00
-- url     : https://prove2.me/submissions/06590698-3d8d-4d75-9c9a-bf1231c25263

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhSurvival
open ActuarialValuation

theorem solution(a b t : ℝ) : nhSurvival a b t t=1 := by
  first
  | (simp [nhSurvival, nhCumulative]; done)
  | (norm_num [nhSurvival, nhCumulative]; done)
  | (unfold nhSurvival nhCumulative; positivity)
  | (simp only [nhSurvival, nhCumulative]; positivity)
  | (unfold nhSurvival nhCumulative; ring)
  | (unfold nhSurvival nhCumulative; simp; done)
  | (unfold nhSurvival nhCumulative; norm_num; done)
  | (simp [nhSurvival, nhCumulative]; ring)
  | (unfold nhSurvival nhCumulative; split_ifs <;> simp_all <;> linarith)
  | (unfold nhSurvival nhCumulative; nlinarith [sq_nonneg 0])
  | (simp_all [nhSurvival, nhCumulative]; done)
  | (unfold nhSurvival nhCumulative; simp_all; done)
  | rfl
