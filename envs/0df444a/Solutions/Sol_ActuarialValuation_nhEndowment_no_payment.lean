-- Prove2me | solution 1 for ActuarialValuation.nhEndowment_no_payment
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:37:36.471712+00:00
-- url     : https://prove2.me/submissions/b0a377e4-3e23-4789-ad59-4cb2b5c5e61e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhEndowment
open ActuarialValuation

theorem solution(a b δ T t : ℝ) : nhEndowment a b δ T 0 t=0 := by
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
