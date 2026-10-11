-- Prove2me | solution 1 for ActuarialValuation.ipPoisson_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:35:00.515556+00:00
-- url     : https://prove2.me/submissions/44ee3951-5ffa-480f-877e-fb8a6aaa0c1f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipPoisson
open ActuarialValuation

theorem solution(l : ℝ) : ipPoisson l 0=Real.exp (-l) := by
  first
  | (simp [ipPoisson]; done)
  | (norm_num [ipPoisson]; done)
  | (unfold ipPoisson; positivity)
  | (simp only [ipPoisson]; positivity)
  | (unfold ipPoisson; ring)
  | (unfold ipPoisson; simp; done)
  | (unfold ipPoisson; norm_num; done)
  | (simp [ipPoisson]; ring)
  | (unfold ipPoisson; split_ifs <;> simp_all <;> linarith)
  | (unfold ipPoisson; nlinarith [sq_nonneg 0])
  | (simp_all [ipPoisson]; done)
  | (unfold ipPoisson; simp_all; done)
  | rfl
