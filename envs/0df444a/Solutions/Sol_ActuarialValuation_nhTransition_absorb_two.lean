-- Prove2me | solution 1 for ActuarialValuation.nhTransition_absorb_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:25:05.608992+00:00
-- url     : https://prove2.me/submissions/3f001ad5-7345-4189-9708-bd2537208872

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhTransition
open ActuarialValuation

theorem solution(a b p s t : ℝ) : nhTransition a b p s t 2 2=1 := by
  first
  | (simp [nhTransition, nhSurvival, nhCumulative, nhExitOne, nhExitTwo]; done)
  | (norm_num [nhTransition, nhSurvival, nhCumulative, nhExitOne, nhExitTwo]; done)
  | (unfold nhTransition nhSurvival nhCumulative nhExitOne nhExitTwo; positivity)
  | (simp only [nhTransition, nhSurvival, nhCumulative, nhExitOne, nhExitTwo]; positivity)
  | (unfold nhTransition nhSurvival nhCumulative nhExitOne nhExitTwo; ring)
  | (unfold nhTransition nhSurvival nhCumulative nhExitOne nhExitTwo; simp; done)
  | (unfold nhTransition nhSurvival nhCumulative nhExitOne nhExitTwo; norm_num; done)
  | (simp [nhTransition, nhSurvival, nhCumulative, nhExitOne, nhExitTwo]; ring)
  | (unfold nhTransition nhSurvival nhCumulative nhExitOne nhExitTwo; split_ifs <;> simp_all <;> linarith)
  | (unfold nhTransition nhSurvival nhCumulative nhExitOne nhExitTwo; nlinarith [sq_nonneg 0])
  | (simp_all [nhTransition, nhSurvival, nhCumulative, nhExitOne, nhExitTwo]; done)
  | (unfold nhTransition nhSurvival nhCumulative nhExitOne nhExitTwo; simp_all; done)
  | rfl
