-- Prove2me | solution 1 for ActuarialValuation.frForce_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:23:00.264505+00:00
-- url     : https://prove2.me/submissions/bb75129a-60e6-4582-892a-65df6aaa584c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frForceSurvival
open ActuarialValuation

theorem solution(mu : ℝ) : frForceSurvival mu 0 = 1 := by
  first
  | (simp [frForceSurvival]; done)
  | (norm_num [frForceSurvival]; done)
  | (unfold frForceSurvival; positivity)
  | (simp only [frForceSurvival]; positivity)
  | (unfold frForceSurvival; ring)
  | (unfold frForceSurvival; simp; done)
  | (unfold frForceSurvival; norm_num; done)
  | (simp [frForceSurvival]; ring)
  | (unfold frForceSurvival; split_ifs <;> simp_all <;> linarith)
  | (unfold frForceSurvival; nlinarith [sq_nonneg 0])
  | (simp_all [frForceSurvival]; done)
  | (unfold frForceSurvival; simp_all; done)
  | rfl
