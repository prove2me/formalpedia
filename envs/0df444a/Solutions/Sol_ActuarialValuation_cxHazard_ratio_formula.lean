-- Prove2me | solution 1 for ActuarialValuation.cxHazard_ratio_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:43:26.209444+00:00
-- url     : https://prove2.me/submissions/a38fd55e-fb93-49c3-8664-5401d4219e1f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxHazardRatio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (base beta z1 z2 : ℝ) (hb : base≠0) : cxHazardRatio base beta z1 z2=Real.exp (beta*(z1-z2)) := by
  have h2 : Real.exp (beta*z2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  rw [show beta*(z1-z2) = beta*z1-beta*z2 by ring, Real.exp_sub]
  unfold cxHazardRatio cxHazard cxRelativeRisk
  field_simp [hb, h2] <;> ring
