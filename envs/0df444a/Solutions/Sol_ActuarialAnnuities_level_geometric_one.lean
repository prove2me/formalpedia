-- Prove2me | solution 1 for ActuarialAnnuities.level_geometric_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:15:12.291862+00:00
-- url     : https://prove2.me/submissions/2f16c902-e8ab-4119-9d8a-14f55c9dc2c9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bLevel
import Definitions.Def_actuarial_bGeometric
open ActuarialAnnuities

theorem solution(a j : ℕ) (c : ℝ) : bGeometric a c 1 j = bLevel c j := by
  first
  | (simp [bLevel, bGeometric]; done)
  | (norm_num [bLevel, bGeometric]; done)
  | (unfold bLevel bGeometric; positivity)
  | (simp only [bLevel, bGeometric]; positivity)
  | (unfold bLevel bGeometric; ring)
  | (unfold bLevel bGeometric; simp; done)
  | (unfold bLevel bGeometric; norm_num; done)
  | (simp [bLevel, bGeometric]; ring)
  | (unfold bLevel bGeometric; split_ifs <;> simp_all <;> linarith)
  | (unfold bLevel bGeometric; nlinarith [sq_nonneg 0])
  | (simp_all [bLevel, bGeometric]; done)
  | (unfold bLevel bGeometric; simp_all; done)
  | rfl
