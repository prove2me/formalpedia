-- Prove2me | solution 1 for ActuarialValuation.cxRelativeRisk_zero_beta
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:53:52.7808+00:00
-- url     : https://prove2.me/submissions/c6dcc52e-842d-44bc-b841-e8552d99ee21

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRelativeRisk
open ActuarialValuation

theorem solution(z : ℝ) : cxRelativeRisk 0 z=1 := by
  first
  | (simp [cxRelativeRisk]; done)
  | (norm_num [cxRelativeRisk]; done)
  | (unfold cxRelativeRisk; positivity)
  | (simp only [cxRelativeRisk]; positivity)
  | (unfold cxRelativeRisk; ring)
  | (unfold cxRelativeRisk; simp; done)
  | (unfold cxRelativeRisk; norm_num; done)
  | (simp [cxRelativeRisk]; ring)
  | (unfold cxRelativeRisk; split_ifs <;> simp_all <;> linarith)
  | (unfold cxRelativeRisk; nlinarith [sq_nonneg 0])
  | (simp_all [cxRelativeRisk]; done)
  | (unfold cxRelativeRisk; simp_all; done)
  | rfl
