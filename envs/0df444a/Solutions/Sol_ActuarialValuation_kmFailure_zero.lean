-- Prove2me | solution 1 for ActuarialValuation.kmFailure_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:26:03.996641+00:00
-- url     : https://prove2.me/submissions/0884207e-7f80-4219-a5d7-37aa5ac28fad

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmFailure
open ActuarialValuation

theorem solution(r d : ℕ → ℝ) : kmFailure r d 0 = 0 := by
  first
  | (simp [kmFailure, kmSurvival, kmSurvivalFactor, kmDeathHazard]; done)
  | (norm_num [kmFailure, kmSurvival, kmSurvivalFactor, kmDeathHazard]; done)
  | (unfold kmFailure kmSurvival kmSurvivalFactor kmDeathHazard; positivity)
  | (simp only [kmFailure, kmSurvival, kmSurvivalFactor, kmDeathHazard]; positivity)
  | (unfold kmFailure kmSurvival kmSurvivalFactor kmDeathHazard; ring)
  | (unfold kmFailure kmSurvival kmSurvivalFactor kmDeathHazard; simp; done)
  | (unfold kmFailure kmSurvival kmSurvivalFactor kmDeathHazard; norm_num; done)
  | (simp [kmFailure, kmSurvival, kmSurvivalFactor, kmDeathHazard]; ring)
  | (unfold kmFailure kmSurvival kmSurvivalFactor kmDeathHazard; split_ifs <;> simp_all <;> linarith)
  | (unfold kmFailure kmSurvival kmSurvivalFactor kmDeathHazard; nlinarith [sq_nonneg 0])
  | (simp_all [kmFailure, kmSurvival, kmSurvivalFactor, kmDeathHazard]; done)
  | (unfold kmFailure kmSurvival kmSurvivalFactor kmDeathHazard; simp_all; done)
  | rfl
