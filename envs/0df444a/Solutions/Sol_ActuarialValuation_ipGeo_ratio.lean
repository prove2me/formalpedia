-- Prove2me | solution 1 for ActuarialValuation.ipGeo_ratio
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:35:20.306246+00:00
-- url     : https://prove2.me/submissions/48dc7731-9f69-459b-abb6-6e10bbe2dbbc

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipGeo
open ActuarialValuation

theorem solution(q : ℝ) (n : ℕ) : ipGeo q (n+1)=q*ipGeo q n := by
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
  | (simp_all [ipGeo]; done)
  | (unfold ipGeo; simp_all; done)
  | rfl
