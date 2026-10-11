-- Prove2me | solution 1 for ActuarialValuation.cxPGF_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:22:57.229916+00:00
-- url     : https://prove2.me/submissions/a7a0291b-e060-428f-b73f-cd700ca16d9c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPGF
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (z : ℝ) : cxPGF f 1 z = f 0 := by
  first
  | (simp [cxPGF]; done)
  | (norm_num [cxPGF]; done)
  | (unfold cxPGF; positivity)
  | (simp only [cxPGF]; positivity)
  | (unfold cxPGF; ring)
  | (unfold cxPGF; simp; done)
  | (unfold cxPGF; norm_num; done)
  | (simp [cxPGF]; ring)
  | (unfold cxPGF; split_ifs <;> simp_all <;> linarith)
  | (unfold cxPGF; nlinarith [sq_nonneg 0])
  | (simp_all [cxPGF]; done)
  | (unfold cxPGF; simp_all; done)
  | rfl
