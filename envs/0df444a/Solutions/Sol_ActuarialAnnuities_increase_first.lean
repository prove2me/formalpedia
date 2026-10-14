-- Prove2me | solution 1 for ActuarialAnnuities.increase_first
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:13:39.351232+00:00
-- url     : https://prove2.me/submissions/e1a15fe0-1527-4805-aeff-a740716a8853

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bIncreasing
open ActuarialAnnuities

theorem solution(a : ℕ) : bIncreasing a a = 1 := by
  first
  | (simp [bIncreasing]; done)
  | (norm_num [bIncreasing]; done)
  | (unfold bIncreasing; positivity)
  | (simp only [bIncreasing]; positivity)
  | (unfold bIncreasing; ring)
  | (unfold bIncreasing; simp; done)
  | (unfold bIncreasing; norm_num; done)
  | (simp [bIncreasing]; ring)
  | (unfold bIncreasing; split_ifs <;> simp_all <;> linarith)
  | (unfold bIncreasing; nlinarith [sq_nonneg 0])
  | (simp_all [bIncreasing]; done)
  | (unfold bIncreasing; simp_all; done)
  | rfl
