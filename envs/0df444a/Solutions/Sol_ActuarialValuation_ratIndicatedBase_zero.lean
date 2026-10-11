-- Prove2me | solution 1 for ActuarialValuation.ratIndicatedBase_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:05:14.617997+00:00
-- url     : https://prove2.me/submissions/53709458-0772-4669-b33a-04a14d62c46b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratIndicatedBase
open ActuarialValuation

theorem solution(w : ℝ) : ratIndicatedBase 0 w = 0 := by
  first
  | (simp [ratIndicatedBase]; done)
  | (norm_num [ratIndicatedBase]; done)
  | (unfold ratIndicatedBase; positivity)
  | (simp only [ratIndicatedBase]; positivity)
  | (unfold ratIndicatedBase; ring)
  | (unfold ratIndicatedBase; simp; done)
  | (unfold ratIndicatedBase; norm_num; done)
  | (simp [ratIndicatedBase]; ring)
  | (unfold ratIndicatedBase; split_ifs <;> simp_all <;> linarith)
  | (unfold ratIndicatedBase; nlinarith [sq_nonneg 0])
  | (simp_all [ratIndicatedBase]; done)
  | (unfold ratIndicatedBase; simp_all; done)
  | rfl
