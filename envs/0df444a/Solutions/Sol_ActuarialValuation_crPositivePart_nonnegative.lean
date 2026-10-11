-- Prove2me | solution 1 for ActuarialValuation.crPositivePart_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:54:04.786807+00:00
-- url     : https://prove2.me/submissions/59721326-3118-42c5-92b8-891b43b58a8a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crPositivePart
open ActuarialValuation

theorem solution(x : ℝ) : 0≤crPositivePart x := by
  first
  | (simp [crPositivePart]; done)
  | (norm_num [crPositivePart]; done)
  | (unfold crPositivePart; positivity)
  | (simp only [crPositivePart]; positivity)
  | (unfold crPositivePart; ring)
  | (unfold crPositivePart; simp; done)
  | (unfold crPositivePart; norm_num; done)
  | (simp [crPositivePart]; ring)
  | (unfold crPositivePart; split_ifs <;> simp_all <;> linarith)
  | (unfold crPositivePart; nlinarith [sq_nonneg 0])
  | (simp_all [crPositivePart]; done)
  | (unfold crPositivePart; simp_all; done)
  | rfl
