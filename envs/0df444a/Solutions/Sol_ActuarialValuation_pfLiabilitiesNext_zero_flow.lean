-- Prove2me | solution 1 for ActuarialValuation.pfLiabilitiesNext_zero_flow
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:40:04.220759+00:00
-- url     : https://prove2.me/submissions/e531f0cc-cd33-4290-b56d-388b8fa5d9c8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfLiabilitiesNext
open ActuarialValuation

theorem solution(liability : ℝ) : pfLiabilitiesNext liability 0 0 0 0=liability := by
  first
  | (simp [pfLiabilitiesNext]; done)
  | (norm_num [pfLiabilitiesNext]; done)
  | (unfold pfLiabilitiesNext; positivity)
  | (simp only [pfLiabilitiesNext]; positivity)
  | (unfold pfLiabilitiesNext; ring)
  | (unfold pfLiabilitiesNext; simp; done)
  | (unfold pfLiabilitiesNext; norm_num; done)
  | (simp [pfLiabilitiesNext]; ring)
  | (unfold pfLiabilitiesNext; split_ifs <;> simp_all <;> linarith)
  | (unfold pfLiabilitiesNext; nlinarith [sq_nonneg 0])
  | (simp_all [pfLiabilitiesNext]; done)
  | (unfold pfLiabilitiesNext; simp_all; done)
  | rfl
