-- Prove2me | solution 1 for ActuarialValuation.nhEndowment_terminal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:17:50.960989+00:00
-- url     : https://prove2.me/submissions/d34322b4-4c6b-4dbf-81c2-17646e7aecd0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhEndowment
open ActuarialValuation

theorem solution(a b δ T B : ℝ) : nhEndowment a b δ T B T=B := by
  first
  | (simp [nhEndowment, nhSurvival, nhCumulative]; done)
  | (norm_num [nhEndowment, nhSurvival, nhCumulative]; done)
  | (unfold nhEndowment nhSurvival nhCumulative; positivity)
  | (simp only [nhEndowment, nhSurvival, nhCumulative]; positivity)
  | (unfold nhEndowment nhSurvival nhCumulative; ring)
  | (unfold nhEndowment nhSurvival nhCumulative; simp; done)
  | (unfold nhEndowment nhSurvival nhCumulative; norm_num; done)
  | (simp [nhEndowment, nhSurvival, nhCumulative]; ring)
  | (unfold nhEndowment nhSurvival nhCumulative; split_ifs <;> simp_all <;> linarith)
  | (unfold nhEndowment nhSurvival nhCumulative; nlinarith [sq_nonneg 0])
  | (simp_all [nhEndowment, nhSurvival, nhCumulative]; done)
  | (unfold nhEndowment nhSurvival nhCumulative; simp_all; done)
  | rfl
