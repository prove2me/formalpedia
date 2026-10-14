-- Prove2me | solution 1 for ActuarialValuation.pfModifiedRate_zero_deficit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:22:36.723658+00:00
-- url     : https://prove2.me/submissions/b14f5fae-3658-4531-8419-0dc19bf5ed2e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfModifiedRate
open ActuarialValuation

theorem solution(normal annuity : ℝ) : pfModifiedRate normal 0 annuity=normal := by
  first
  | (simp [pfModifiedRate, pfAmortisation]; done)
  | (norm_num [pfModifiedRate, pfAmortisation]; done)
  | (unfold pfModifiedRate pfAmortisation; positivity)
  | (simp only [pfModifiedRate, pfAmortisation]; positivity)
  | (unfold pfModifiedRate pfAmortisation; ring)
  | (unfold pfModifiedRate pfAmortisation; simp; done)
  | (unfold pfModifiedRate pfAmortisation; norm_num; done)
  | (simp [pfModifiedRate, pfAmortisation]; ring)
  | (unfold pfModifiedRate pfAmortisation; split_ifs <;> simp_all <;> linarith)
  | (unfold pfModifiedRate pfAmortisation; nlinarith [sq_nonneg 0])
  | (simp_all [pfModifiedRate, pfAmortisation]; done)
  | (unfold pfModifiedRate pfAmortisation; simp_all; done)
  | rfl
