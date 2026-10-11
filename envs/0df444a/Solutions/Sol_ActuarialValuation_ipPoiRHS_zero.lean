-- Prove2me | solution 1 for ActuarialValuation.ipPoiRHS_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:56:41.284213+00:00
-- url     : https://prove2.me/submissions/3a56bca3-a1d0-4210-a255-ab5dde7f95ae

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipPoiRHS
open ActuarialValuation

theorem solution(l : ℝ) (f g : ℕ → ℝ) : ipPoiRHS l f g 0=0 := by
  first
  | (simp [ipPoiRHS]; done)
  | (norm_num [ipPoiRHS]; done)
  | (unfold ipPoiRHS; positivity)
  | (simp only [ipPoiRHS]; positivity)
  | (unfold ipPoiRHS; ring)
  | (unfold ipPoiRHS; simp; done)
  | (unfold ipPoiRHS; norm_num; done)
  | (simp [ipPoiRHS]; ring)
  | (unfold ipPoiRHS; split_ifs <;> simp_all <;> linarith)
  | (unfold ipPoiRHS; nlinarith [sq_nonneg 0])
  | (simp_all [ipPoiRHS]; done)
  | (unfold ipPoiRHS; simp_all; done)
  | rfl
