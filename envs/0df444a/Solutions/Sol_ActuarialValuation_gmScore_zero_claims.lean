-- Prove2me | solution 1 for ActuarialValuation.gmScore_zero_claims
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:39:43.385506+00:00
-- url     : https://prove2.me/submissions/793afccc-fc88-495b-b21f-9d58127b3a81

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmScore
open ActuarialValuation

theorem solution(exposure eta : ℝ) : gmScore 0 exposure eta= -gmMean exposure eta := by
  first
  | (simp [gmMean, gmScore]; done)
  | (norm_num [gmMean, gmScore]; done)
  | (unfold gmMean gmScore; positivity)
  | (simp only [gmMean, gmScore]; positivity)
  | (unfold gmMean gmScore; ring)
  | (unfold gmMean gmScore; simp; done)
  | (unfold gmMean gmScore; norm_num; done)
  | (simp [gmMean, gmScore]; ring)
  | (unfold gmMean gmScore; split_ifs <;> simp_all <;> linarith)
  | (unfold gmMean gmScore; nlinarith [sq_nonneg 0])
  | (simp_all [gmMean, gmScore]; done)
  | (unfold gmMean gmScore; simp_all; done)
  | rfl
