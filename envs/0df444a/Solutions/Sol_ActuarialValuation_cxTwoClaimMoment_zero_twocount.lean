-- Prove2me | solution 1 for ActuarialValuation.cxTwoClaimMoment_zero_twocount
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:17:52.693587+00:00
-- url     : https://prove2.me/submissions/84e08f78-9506-417a-922e-1dad4e2266ef

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxTwoClaimMoment
open ActuarialValuation

theorem solution(mu m2 p1 : ℝ) : cxTwoClaimMoment mu m2 p1 0 = p1*m2 := by
  first
  | (simp [cxTwoClaimMoment]; done)
  | (norm_num [cxTwoClaimMoment]; done)
  | (unfold cxTwoClaimMoment; positivity)
  | (simp only [cxTwoClaimMoment]; positivity)
  | (unfold cxTwoClaimMoment; ring)
  | (unfold cxTwoClaimMoment; simp; done)
  | (unfold cxTwoClaimMoment; norm_num; done)
  | (simp [cxTwoClaimMoment]; ring)
  | (unfold cxTwoClaimMoment; split_ifs <;> simp_all <;> linarith)
  | (unfold cxTwoClaimMoment; nlinarith [sq_nonneg 0])
  | (simp_all [cxTwoClaimMoment]; done)
  | (unfold cxTwoClaimMoment; simp_all; done)
  | rfl
