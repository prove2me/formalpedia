-- Prove2me | solution 1 for ActuarialValuation.cxRiskDenom_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:24:15.40044+00:00
-- url     : https://prove2.me/submissions/ab106214-1eb8-4c75-81a4-3b01e402568a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRiskDenom
open ActuarialValuation

theorem solution{n : ℕ} (beta : ℝ) (risk : Finset (Fin n)) (z : Fin n → ℝ) : 0 ≤ cxRiskDenom beta risk z := by
  first
  | (simp [cxRiskDenom, cxRelativeRisk]; done)
  | (norm_num [cxRiskDenom, cxRelativeRisk]; done)
  | (unfold cxRiskDenom cxRelativeRisk; positivity)
  | (simp only [cxRiskDenom, cxRelativeRisk]; positivity)
  | (unfold cxRiskDenom cxRelativeRisk; ring)
  | (unfold cxRiskDenom cxRelativeRisk; simp; done)
  | (unfold cxRiskDenom cxRelativeRisk; norm_num; done)
  | (simp [cxRiskDenom, cxRelativeRisk]; ring)
  | (unfold cxRiskDenom cxRelativeRisk; split_ifs <;> simp_all <;> linarith)
  | (unfold cxRiskDenom cxRelativeRisk; nlinarith [sq_nonneg 0])
  | (simp_all [cxRiskDenom, cxRelativeRisk]; done)
  | (unfold cxRiskDenom cxRelativeRisk; simp_all; done)
  | rfl
