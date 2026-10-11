-- Prove2me | solution 1 for ActuarialValuation.nhExitTwo_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:35:03.471396+00:00
-- url     : https://prove2.me/submissions/94b34234-94fb-4f95-a043-9bfe1626447c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhExitTwo
open ActuarialValuation

theorem solution(a b p t : ℝ) : nhExitTwo a b p t t=0 := by
  first
  | (simp [nhExitTwo, nhSurvival, nhCumulative]; done)
  | (norm_num [nhExitTwo, nhSurvival, nhCumulative]; done)
  | (unfold nhExitTwo nhSurvival nhCumulative; positivity)
  | (simp only [nhExitTwo, nhSurvival, nhCumulative]; positivity)
  | (unfold nhExitTwo nhSurvival nhCumulative; ring)
  | (unfold nhExitTwo nhSurvival nhCumulative; simp; done)
  | (unfold nhExitTwo nhSurvival nhCumulative; norm_num; done)
  | (simp [nhExitTwo, nhSurvival, nhCumulative]; ring)
  | (unfold nhExitTwo nhSurvival nhCumulative; split_ifs <;> simp_all <;> linarith)
  | (unfold nhExitTwo nhSurvival nhCumulative; nlinarith [sq_nonneg 0])
  | (simp_all [nhExitTwo, nhSurvival, nhCumulative]; done)
  | (unfold nhExitTwo nhSurvival nhCumulative; simp_all; done)
  | rfl
