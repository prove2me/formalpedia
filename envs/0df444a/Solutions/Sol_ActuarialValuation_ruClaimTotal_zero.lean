-- Prove2me | solution 1 for ActuarialValuation.ruClaimTotal_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:39:03.842218+00:00
-- url     : https://prove2.me/submissions/9bf7fe21-a943-4149-b55d-c6faa8e6c858

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruClaimTotal
open ActuarialValuation

theorem solution(x : ℕ → ℝ) : ruClaimTotal x 0 = 0 := by
  first
  | (simp [ruClaimTotal]; done)
  | (norm_num [ruClaimTotal]; done)
  | (unfold ruClaimTotal; positivity)
  | (simp only [ruClaimTotal]; positivity)
  | (unfold ruClaimTotal; ring)
  | (unfold ruClaimTotal; simp; done)
  | (unfold ruClaimTotal; norm_num; done)
  | (simp [ruClaimTotal]; ring)
  | (unfold ruClaimTotal; split_ifs <;> simp_all <;> linarith)
  | (unfold ruClaimTotal; nlinarith [sq_nonneg 0])
  | (simp_all [ruClaimTotal]; done)
  | (unfold ruClaimTotal; simp_all; done)
  | rfl
