-- Prove2me | solution 1 for ActuarialValuation.irCostUltimate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:10:12.79473+00:00
-- url     : https://prove2.me/submissions/240bcb54-3ba9-421d-b1f1-a2006e905037

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irClaimCostUltimate
open ActuarialValuation

theorem solution(avg factor : ℝ) (ha : 0 ≤ avg) (hf : 0 ≤ factor) : 0 ≤ irClaimCostUltimate avg factor := by
  first
  | (simp [irClaimCostUltimate]; done)
  | (norm_num [irClaimCostUltimate]; done)
  | (unfold irClaimCostUltimate; positivity)
  | (simp only [irClaimCostUltimate]; positivity)
  | (unfold irClaimCostUltimate; ring)
  | (unfold irClaimCostUltimate; simp; done)
  | (unfold irClaimCostUltimate; norm_num; done)
  | (simp [irClaimCostUltimate]; ring)
  | (unfold irClaimCostUltimate; split_ifs <;> simp_all <;> linarith)
  | (unfold irClaimCostUltimate; nlinarith [sq_nonneg 0])
  | (simp_all [irClaimCostUltimate]; done)
  | (unfold irClaimCostUltimate; simp_all; done)
  | rfl
