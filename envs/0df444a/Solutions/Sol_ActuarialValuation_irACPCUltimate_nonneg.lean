-- Prove2me | solution 1 for ActuarialValuation.irACPCUltimate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:51:33.933558+00:00
-- url     : https://prove2.me/submissions/4f84704c-d74b-47ae-a122-faf5afd05905

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irACPCUltimate
open ActuarialValuation

theorem solution(count avg : ℝ) (hc : 0 ≤ count) (ha : 0 ≤ avg) : 0 ≤ irACPCUltimate count avg := by
  first
  | (simp [irACPCUltimate]; done)
  | (norm_num [irACPCUltimate]; done)
  | (unfold irACPCUltimate; positivity)
  | (simp only [irACPCUltimate]; positivity)
  | (unfold irACPCUltimate; ring)
  | (unfold irACPCUltimate; simp; done)
  | (unfold irACPCUltimate; norm_num; done)
  | (simp [irACPCUltimate]; ring)
  | (unfold irACPCUltimate; split_ifs <;> simp_all <;> linarith)
  | (unfold irACPCUltimate; nlinarith [sq_nonneg 0])
  | (simp_all [irACPCUltimate]; done)
  | (unfold irACPCUltimate; simp_all; done)
  | rfl
