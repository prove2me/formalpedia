-- Prove2me | solution 1 for ActuarialValuation.coCopula_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:30:29.237974+00:00
-- url     : https://prove2.me/submissions/c14906f1-30fc-458a-aaa8-9b57d45f041e

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coUpper
import Definitions.Def_actuarial_coIsCopula

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (C : ℝ → ℝ → ℝ) (hc : coIsCopula C) (u v : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hv0 : 0≤v) (hv1 : v≤1) : C u v≤coUpper u v := by
  rcases hc with ⟨hm, hr⟩
  have hCu0 : C u 0 = 0 := (hm u hu0 hu1).1
  have hC0v : C 0 v = 0 := (hm v hv0 hv1).2.1
  have hC01 : C 0 1 = 0 := (hm 1 zero_le_one le_rfl).2.1
  have hC10 : C 1 0 = 0 := (hm 0 le_rfl zero_le_one).2.2.2
  have hCu1 : C u 1 = u := (hm u hu0 hu1).2.2.1
  have hC1v : C 1 v = v := (hm v hv0 hv1).2.2.2
  have hu := hr 0 u v 1 le_rfl hu0 hu1 hv0 hv1 le_rfl
  unfold coRectangle at hu
  rw [hCu1, hC01, hC0v] at hu
  have hv := hr u 1 0 v hu0 hu1 le_rfl le_rfl hv0 hv1
  unfold coRectangle at hv
  rw [hC1v, hC10, hCu0] at hv
  unfold coUpper
  apply le_min <;> linarith
