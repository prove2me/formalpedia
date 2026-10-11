-- Prove2me | solution 1 for ActuarialValuation.gmMean_zero_exposure
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:05:50.471969+00:00
-- url     : https://prove2.me/submissions/cf275bb6-b997-408c-a27e-0391bd05faba

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean
open ActuarialValuation

theorem solution(eta : ℝ) : gmMean 0 eta=0 := by
  first
  | (simp [gmMean]; done)
  | (norm_num [gmMean]; done)
  | (unfold gmMean; positivity)
  | (simp only [gmMean]; positivity)
  | (unfold gmMean; ring)
  | (unfold gmMean; simp; done)
  | (unfold gmMean; norm_num; done)
  | (simp [gmMean]; ring)
  | (unfold gmMean; split_ifs <;> simp_all <;> linarith)
  | (unfold gmMean; nlinarith [sq_nonneg 0])
  | (simp_all [gmMean]; done)
  | (unfold gmMean; simp_all; done)
  | rfl
