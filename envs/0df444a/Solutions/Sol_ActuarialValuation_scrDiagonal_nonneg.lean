-- Prove2me | solution 1 for ActuarialValuation.scrDiagonal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:02:10.910312+00:00
-- url     : https://prove2.me/submissions/02178266-1d2f-48cb-91b4-5be12b19f205

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrDiagonal
open ActuarialValuation

theorem solution(c : ℝ) : 0 ≤ scrDiagonal c := by
  first
  | (simp [scrDiagonal]; done)
  | (norm_num [scrDiagonal]; done)
  | (unfold scrDiagonal; positivity)
  | (simp only [scrDiagonal]; positivity)
  | (unfold scrDiagonal; ring)
  | (unfold scrDiagonal; simp; done)
  | (unfold scrDiagonal; norm_num; done)
  | (simp [scrDiagonal]; ring)
  | (unfold scrDiagonal; split_ifs <;> simp_all <;> linarith)
  | (unfold scrDiagonal; nlinarith [sq_nonneg 0])
  | rfl
