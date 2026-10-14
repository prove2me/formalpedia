-- Prove2me | solution 1 for ActuarialValuation.ruRetained_le_claim
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:42:21.563286+00:00
-- url     : https://prove2.me/submissions/8643ebe3-b50e-4e96-a4dd-6d76862877b0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruRetained
open ActuarialValuation

theorem solution(x d : ℝ) : ruRetained x d ≤ x := by
  first
  | (simp [ruRetained]; done)
  | (norm_num [ruRetained]; done)
  | (unfold ruRetained; positivity)
  | (simp only [ruRetained]; positivity)
  | (unfold ruRetained; ring)
  | (unfold ruRetained; simp; done)
  | (unfold ruRetained; norm_num; done)
  | (simp [ruRetained]; ring)
  | (unfold ruRetained; split_ifs <;> simp_all <;> linarith)
  | (unfold ruRetained; nlinarith [sq_nonneg 0])
  | (simp_all [ruRetained]; done)
  | (unfold ruRetained; simp_all; done)
  | rfl
