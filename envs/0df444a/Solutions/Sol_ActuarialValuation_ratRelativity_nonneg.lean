-- Prove2me | solution 1 for ActuarialValuation.ratRelativity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:23:46.685312+00:00
-- url     : https://prove2.me/submissions/2b715370-d3f9-4740-ae92-5c2e6332e8c7

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratRelativity
open ActuarialValuation

theorem solution(c base : ℝ) (hc : 0 ≤ c) (hb : 0 < base) : 0 ≤ ratRelativity c base := by
  first
  | (simp [ratRelativity]; done)
  | (norm_num [ratRelativity]; done)
  | (unfold ratRelativity; positivity)
  | (simp only [ratRelativity]; positivity)
  | (unfold ratRelativity; ring)
  | (unfold ratRelativity; simp; done)
  | (unfold ratRelativity; norm_num; done)
  | (simp [ratRelativity]; ring)
  | (unfold ratRelativity; split_ifs <;> simp_all <;> linarith)
  | (unfold ratRelativity; nlinarith [sq_nonneg 0])
  | (simp_all [ratRelativity]; done)
  | (unfold ratRelativity; simp_all; done)
  | rfl
