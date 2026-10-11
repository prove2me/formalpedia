-- Prove2me | solution 1 for ActuarialValuation.scrDiagonal_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:42:04.34527+00:00
-- url     : https://prove2.me/submissions/98898513-fd4c-4cc1-b972-0e3ba339d69c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrDiagonal
open ActuarialValuation

theorem solution: scrDiagonal 0 = 0 := by
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
