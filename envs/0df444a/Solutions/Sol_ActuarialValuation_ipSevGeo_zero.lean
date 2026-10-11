-- Prove2me | solution 1 for ActuarialValuation.ipSevGeo_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:45:47.605553+00:00
-- url     : https://prove2.me/submissions/4e86d1a9-f595-4f72-8319-8f0b65962512

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipSevGeo
open ActuarialValuation

theorem solution(r : ℝ) : ipSevGeo r 0=1-r := by
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
  | rfl
