-- Prove2me | solution 1 for ActuarialValuation.cxRiskMean_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:29:13.575262+00:00
-- url     : https://prove2.me/submissions/2f091adc-47e6-4b74-b2e8-f612527e0c90

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRiskMean
open ActuarialValuation

theorem solution{n : ℕ} (beta : ℝ) (risk : Finset (Fin n)) : cxRiskMean beta risk (fun _ => 0)=0 := by
  first
  | (simp [cxRiskMean, cxRiskDenom, cxRelativeRisk, cxRiskWeighted]; done)
  | (norm_num [cxRiskMean, cxRiskDenom, cxRelativeRisk, cxRiskWeighted]; done)
  | (unfold cxRiskMean cxRiskDenom cxRelativeRisk cxRiskWeighted; positivity)
  | (simp only [cxRiskMean, cxRiskDenom, cxRelativeRisk, cxRiskWeighted]; positivity)
  | (unfold cxRiskMean cxRiskDenom cxRelativeRisk cxRiskWeighted; ring)
  | (unfold cxRiskMean cxRiskDenom cxRelativeRisk cxRiskWeighted; simp; done)
  | (unfold cxRiskMean cxRiskDenom cxRelativeRisk cxRiskWeighted; norm_num; done)
  | (simp [cxRiskMean, cxRiskDenom, cxRelativeRisk, cxRiskWeighted]; ring)
  | (unfold cxRiskMean cxRiskDenom cxRelativeRisk cxRiskWeighted; split_ifs <;> simp_all <;> linarith)
  | (unfold cxRiskMean cxRiskDenom cxRelativeRisk cxRiskWeighted; nlinarith [sq_nonneg 0])
  | (simp_all [cxRiskMean, cxRiskDenom, cxRelativeRisk, cxRiskWeighted]; done)
  | (unfold cxRiskMean cxRiskDenom cxRelativeRisk cxRiskWeighted; simp_all; done)
  | rfl
