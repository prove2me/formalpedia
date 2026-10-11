-- Prove2me | solution 1 for ActuarialValuation.cxPGF_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:15:48.445398+00:00
-- url     : https://prove2.me/submissions/39e84894-6483-4f25-a79b-ac3579c75ac1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPGF
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (z : ℝ) : cxPGF f 0 z = 0 := by
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
