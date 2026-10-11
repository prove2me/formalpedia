-- Prove2me | solution 1 for ActuarialValuation.ipGeo_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:41:58.346581+00:00
-- url     : https://prove2.me/submissions/8225aa50-2c50-4ebf-a778-7341f3b6b5df

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipGeo
open ActuarialValuation

theorem solution(q : ℝ) : ipGeo q 0=1-q := by
  first
  | (simp [ipGeo]; done)
  | (norm_num [ipGeo]; done)
  | (unfold ipGeo; positivity)
  | (simp only [ipGeo]; positivity)
  | (unfold ipGeo; ring)
  | (unfold ipGeo; simp; done)
  | (unfold ipGeo; norm_num; done)
  | (simp [ipGeo]; ring)
  | (unfold ipGeo; split_ifs <;> simp_all <;> linarith)
  | (unfold ipGeo; nlinarith [sq_nonneg 0])
  | rfl
