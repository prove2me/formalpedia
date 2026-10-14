-- Prove2me | solution 1 for ActuarialAnnuities.alive_initial
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:25:16.671776+00:00
-- url     : https://prove2.me/submissions/448e1a76-9e3c-411d-a6a3-b2e9fcb767b2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bAlive
open ActuarialAnnuities

theorem solution(k : ℕ) : bAlive k 0 = 1 := by
  first
  | (simp [bAlive]; done)
  | (norm_num [bAlive]; done)
  | (unfold bAlive; positivity)
  | (simp only [bAlive]; positivity)
  | (unfold bAlive; ring)
  | (unfold bAlive; simp; done)
  | (unfold bAlive; norm_num; done)
  | (simp [bAlive]; ring)
  | (unfold bAlive; split_ifs <;> simp_all <;> linarith)
  | (unfold bAlive; nlinarith [sq_nonneg 0])
  | (simp_all [bAlive]; done)
  | (unfold bAlive; simp_all; done)
  | rfl
