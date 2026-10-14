-- Prove2me | solution 1 for ActuarialValuation.coTailJoint_monotone_v
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:32:47.68254+00:00
-- url     : https://prove2.me/submissions/e7e182a8-c0ec-46ce-a1c3-3bc7480155d3

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coIsCopula
import Definitions.Def_actuarial_coTailJoint

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (C : ℝ → ℝ → ℝ) (hc : coIsCopula C) (u v1 v2 : ℝ) (hu : 0≤u) (hU : u≤1) (hv1 : 0≤v1) (hv : v1≤v2) (hv2 : v2≤1) : coTailJoint C u v2≤coTailJoint C u v1 := by
  rcases hc with ⟨hm, hr⟩
  have hc0 := (hm v1 hv1 (le_trans hv hv2)).2.2.2
  have hc1 := (hm v2 (le_trans hv1 hv) hv2).2.2.2
  have hrect := hr u 1 v1 v2 hu hU le_rfl hv1 hv hv2
  unfold coRectangle at hrect
  rw [hc0, hc1] at hrect
  unfold coTailJoint
  linarith
