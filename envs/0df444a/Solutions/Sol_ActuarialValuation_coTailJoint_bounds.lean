-- Prove2me | solution 1 for ActuarialValuation.coTailJoint_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:34:35.44214+00:00
-- url     : https://prove2.me/submissions/eca90142-283c-4c54-89c5-508820519438

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

theorem solution (C : ℝ → ℝ → ℝ) (hc : coIsCopula C) (u v : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hv0 : 0≤v) (hv1 : v≤1) : 0≤coTailJoint C u v ∧ coTailJoint C u v≤1 := by
  rcases hc with ⟨hm, hr⟩
  have hCu1 : C u 1 = u := (hm u hu0 hu1).2.2.1
  have hC1v : C 1 v = v := (hm v hv0 hv1).2.2.2
  have hC11 : C 1 1 = 1 := (hm 1 zero_le_one le_rfl).2.2.1
  have hC0v : C 0 v = 0 := (hm v hv0 hv1).2.1
  have hC01 : C 0 1 = 0 := (hm 1 zero_le_one le_rfl).2.1
  have hlower := hr u 1 v 1 hu0 hu1 le_rfl hv0 hv1 le_rfl
  unfold coRectangle at hlower
  rw [hC11, hCu1, hC1v] at hlower
  have hupper := hr 0 u v 1 le_rfl hu0 hu1 hv0 hv1 le_rfl
  unfold coRectangle at hupper
  rw [hCu1, hC01, hC0v] at hupper
  unfold coTailJoint
  constructor <;> linarith
