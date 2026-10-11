-- Prove2me | solution 1 for ActuarialValuation.ratClaimsSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:39:18.830969+00:00
-- url     : https://prove2.me/submissions/684daf31-14ec-45a3-9d12-d5295a271ccb

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClaimsSum
open ActuarialValuation

theorem solution(l : ℕ → ℝ) : ratClaimsSum l 0 = 0 := by
  first
  | (simp [ratClaimsSum]; done)
  | (norm_num [ratClaimsSum]; done)
  | (unfold ratClaimsSum; positivity)
  | (simp only [ratClaimsSum]; positivity)
  | (unfold ratClaimsSum; ring)
  | (unfold ratClaimsSum; simp; done)
  | (unfold ratClaimsSum; norm_num; done)
  | (simp [ratClaimsSum]; ring)
  | (unfold ratClaimsSum; split_ifs <;> simp_all <;> linarith)
  | (unfold ratClaimsSum; nlinarith [sq_nonneg 0])
  | (simp_all [ratClaimsSum]; done)
  | (unfold ratClaimsSum; simp_all; done)
  | rfl
