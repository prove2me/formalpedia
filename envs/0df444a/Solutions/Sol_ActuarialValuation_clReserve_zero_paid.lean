-- Prove2me | solution 1 for ActuarialValuation.clReserve_zero_paid
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:05:53.392973+00:00
-- url     : https://prove2.me/submissions/fd807b67-7486-47c8-a1d1-26bc080fd0c1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clReserve
open ActuarialValuation

theorem solution(f : ℝ) : clReserve 0 f = 0 := by
  first
  | (simp [clReserve, clUltimate]; done)
  | (norm_num [clReserve, clUltimate]; done)
  | (unfold clReserve clUltimate; positivity)
  | (simp only [clReserve, clUltimate]; positivity)
  | (unfold clReserve clUltimate; ring)
  | (unfold clReserve clUltimate; simp; done)
  | (unfold clReserve clUltimate; norm_num; done)
  | (simp [clReserve, clUltimate]; ring)
  | (unfold clReserve clUltimate; split_ifs <;> simp_all <;> linarith)
  | (unfold clReserve clUltimate; nlinarith [sq_nonneg 0])
  | (simp_all [clReserve, clUltimate]; done)
  | (unfold clReserve clUltimate; simp_all; done)
  | rfl
