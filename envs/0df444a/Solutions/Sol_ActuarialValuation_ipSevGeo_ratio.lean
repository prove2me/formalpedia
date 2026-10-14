-- Prove2me | solution 1 for ActuarialValuation.ipSevGeo_ratio
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:17:53.033828+00:00
-- url     : https://prove2.me/submissions/1dca55e4-c9c7-4f26-b3c4-835325e2a85b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipSevGeo
open ActuarialValuation

theorem solution(r : ℝ) (k : ℕ) : ipSevGeo r (k+1)=r*ipSevGeo r k := by
  first
  | (simp [ipSevGeo]; done)
  | (norm_num [ipSevGeo]; done)
  | (unfold ipSevGeo; positivity)
  | (simp only [ipSevGeo]; positivity)
  | (unfold ipSevGeo; ring)
  | (unfold ipSevGeo; simp; done)
  | (unfold ipSevGeo; norm_num; done)
  | (simp [ipSevGeo]; ring)
  | (unfold ipSevGeo; split_ifs <;> simp_all <;> linarith)
  | (unfold ipSevGeo; nlinarith [sq_nonneg 0])
  | (simp_all [ipSevGeo]; done)
  | (unfold ipSevGeo; simp_all; done)
  | rfl
