-- Prove2me | solution 1 for ActuarialValuation.coCopula_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:30:15.259494+00:00
-- url     : https://prove2.me/submissions/b37533d0-8ac0-425b-8943-a890e6d8c2a4

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coLower
import Definitions.Def_actuarial_coIsCopula

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (C : ℝ → ℝ → ℝ) (hc : coIsCopula C) (u v : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hv0 : 0≤v) (hv1 : v≤1) : coLower u v≤C u v := by
  rcases hc with ⟨hm, hr⟩
  have hCu0 : C u 0 = 0 := (hm u hu0 hu1).1
  have hC0v : C 0 v = 0 := (hm v hv0 hv1).2.1
  have hC00 : C 0 0 = 0 := (hm 0 le_rfl zero_le_one).1
  have hCu1 : C u 1 = u := (hm u hu0 hu1).2.2.1
  have hC1v : C 1 v = v := (hm v hv0 hv1).2.2.2
  have hC11 : C 1 1 = 1 := (hm 1 zero_le_one le_rfl).2.2.1
  have hnonneg := hr 0 u 0 v le_rfl hu0 hu1 le_rfl hv0 hv1
  unfold coRectangle at hnonneg
  rw [hC0v, hCu0, hC00] at hnonneg
  have hlower := hr u 1 v 1 hu0 hu1 le_rfl hv0 hv1 le_rfl
  unfold coRectangle at hlower
  rw [hC11, hCu1, hC1v] at hlower
  unfold coLower
  apply max_le <;> linarith
