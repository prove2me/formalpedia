-- Prove2me | solution 1 for ActuarialValuation.gmInformation_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:21:40.481207+00:00
-- url     : https://prove2.me/submissions/76bd5176-7495-4d80-b7bb-b6205bd390c2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmInformation
open ActuarialValuation

theorem solution(exposure eta : ℝ) (h : 0 < exposure) : 0 < gmInformation exposure eta := by
  first
  | (simp [gmInformation, gmMean]; done)
  | (norm_num [gmInformation, gmMean]; done)
  | (unfold gmInformation gmMean; positivity)
  | (simp only [gmInformation, gmMean]; positivity)
  | (unfold gmInformation gmMean; ring)
  | (unfold gmInformation gmMean; simp; done)
  | (unfold gmInformation gmMean; norm_num; done)
  | (simp [gmInformation, gmMean]; ring)
  | (unfold gmInformation gmMean; split_ifs <;> simp_all <;> linarith)
  | (unfold gmInformation gmMean; nlinarith [sq_nonneg 0])
  | (simp_all [gmInformation, gmMean]; done)
  | (unfold gmInformation gmMean; simp_all; done)
  | rfl
