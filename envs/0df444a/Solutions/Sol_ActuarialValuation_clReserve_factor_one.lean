-- Prove2me | solution 1 for ActuarialValuation.clReserve_factor_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:15:54.403092+00:00
-- url     : https://prove2.me/submissions/2b86e053-d1da-4809-975a-ab59cf3e9f59

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clReserve
open ActuarialValuation

theorem solution(p : ℝ) : clReserve p 1 = 0 := by
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
