-- Prove2me | solution 1 for ActuarialValuation.pgCountPGF_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:41:31.540138+00:00
-- url     : https://prove2.me/submissions/710d2069-c5f0-4b1c-8576-99af54003929

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgCountPGF
open ActuarialValuation

theorem solution(p : ℕ → ℝ) (m : ℕ) : pgCountPGF p m 1 = ∑ j ∈ Finset.range (m+1), p j := by
  first
  | (simp [pgCountPGF]; done)
  | (norm_num [pgCountPGF]; done)
  | (unfold pgCountPGF; positivity)
  | (simp only [pgCountPGF]; positivity)
  | (unfold pgCountPGF; ring)
  | (unfold pgCountPGF; simp; done)
  | (unfold pgCountPGF; norm_num; done)
  | (simp [pgCountPGF]; ring)
  | (unfold pgCountPGF; split_ifs <;> simp_all <;> linarith)
  | (unfold pgCountPGF; nlinarith [sq_nonneg 0])
  | (simp_all [pgCountPGF]; done)
  | (unfold pgCountPGF; simp_all; done)
  | rfl
