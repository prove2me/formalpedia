-- Prove2me | solution 1 for ActuarialValuation.nhExitOne_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:35:06.408622+00:00
-- url     : https://prove2.me/submissions/3d6feaf8-2998-42e9-904e-746f273f830d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhExitOne
open ActuarialValuation

theorem solution(a b p t : ℝ) : nhExitOne a b p t t=0 := by
  first
  | (simp [nhExitOne, nhSurvival, nhCumulative]; done)
  | (norm_num [nhExitOne, nhSurvival, nhCumulative]; done)
  | (unfold nhExitOne nhSurvival nhCumulative; positivity)
  | (simp only [nhExitOne, nhSurvival, nhCumulative]; positivity)
  | (unfold nhExitOne nhSurvival nhCumulative; ring)
  | (unfold nhExitOne nhSurvival nhCumulative; simp; done)
  | (unfold nhExitOne nhSurvival nhCumulative; norm_num; done)
  | (simp [nhExitOne, nhSurvival, nhCumulative]; ring)
  | (unfold nhExitOne nhSurvival nhCumulative; split_ifs <;> simp_all <;> linarith)
  | (unfold nhExitOne nhSurvival nhCumulative; nlinarith [sq_nonneg 0])
  | (simp_all [nhExitOne, nhSurvival, nhCumulative]; done)
  | (unfold nhExitOne nhSurvival nhCumulative; simp_all; done)
  | rfl
