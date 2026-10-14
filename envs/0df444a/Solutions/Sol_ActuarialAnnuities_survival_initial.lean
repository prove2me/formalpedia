-- Prove2me | solution 1 for ActuarialAnnuities.survival_initial
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:15:01.409993+00:00
-- url     : https://prove2.me/submissions/1989b2b9-5fa5-4e9b-9b52-7231e787bad2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bSurvival
open ActuarialAnnuities

theorem solution(h : ℕ) (p : ℕ → ℝ) : bSurvival h p 0 = bTotal h p := by
  first
  | (simp [bTotal, bSurvival, bAlive]; done)
  | (norm_num [bTotal, bSurvival, bAlive]; done)
  | (unfold bTotal bSurvival bAlive; positivity)
  | (simp only [bTotal, bSurvival, bAlive]; positivity)
  | (unfold bTotal bSurvival bAlive; ring)
  | (unfold bTotal bSurvival bAlive; simp; done)
  | (unfold bTotal bSurvival bAlive; norm_num; done)
  | (simp [bTotal, bSurvival, bAlive]; ring)
  | (unfold bTotal bSurvival bAlive; split_ifs <;> simp_all <;> linarith)
  | (unfold bTotal bSurvival bAlive; nlinarith [sq_nonneg 0])
  | (simp_all [bTotal, bSurvival, bAlive]; done)
  | (unfold bTotal bSurvival bAlive; simp_all; done)
  | rfl
