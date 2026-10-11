-- Prove2me | solution 1 for ActuarialValuation.cxHazard_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:11:29.668459+00:00
-- url     : https://prove2.me/submissions/5a2cadf7-4d99-47a2-a9a8-3c1561b15611

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxHazard
open ActuarialValuation

theorem solution(beta z : ℝ) : cxHazard 0 beta z=0 := by
  first
  | (simp [cxHazard, cxRelativeRisk]; done)
  | (norm_num [cxHazard, cxRelativeRisk]; done)
  | (unfold cxHazard cxRelativeRisk; positivity)
  | (simp only [cxHazard, cxRelativeRisk]; positivity)
  | (unfold cxHazard cxRelativeRisk; ring)
  | (unfold cxHazard cxRelativeRisk; simp; done)
  | (unfold cxHazard cxRelativeRisk; norm_num; done)
  | (simp [cxHazard, cxRelativeRisk]; ring)
  | (unfold cxHazard cxRelativeRisk; split_ifs <;> simp_all <;> linarith)
  | (unfold cxHazard cxRelativeRisk; nlinarith [sq_nonneg 0])
  | (simp_all [cxHazard, cxRelativeRisk]; done)
  | (unfold cxHazard cxRelativeRisk; simp_all; done)
  | rfl
