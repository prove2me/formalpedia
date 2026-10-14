-- Prove2me | solution 1 for ActuarialValuation.coCopulaRisk_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:31:50.592738+00:00
-- url     : https://prove2.me/submissions/c27d4256-f8c2-41b9-947a-c0f9a5db2b5c

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coUpper
import Definitions.Def_actuarial_coLower
import Definitions.Def_actuarial_coFGM
import Definitions.Def_actuarial_coIsCopula
import Definitions.Def_actuarial_coTailJoint

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (theta u v : ℝ) (ht0 : -1≤theta) (ht1 : theta≤1) (hu0 : 0≤u) (hu1 : u≤1) (hv0 : 0≤v) (hv1 : v≤1) : coIsCopula (coFGM theta) ∧ (coLower u v≤coFGM theta u v) ∧ (coFGM theta u v≤coUpper u v) ∧ (coTailJoint (coFGM theta) u v=(1-u)*(1-v)+theta*u*v*(1-u)*(1-v)) := by
  let C : ℝ → ℝ → ℝ := coFGM theta
  have hcop : coIsCopula C := by
    change coIsCopula (coFGM theta)
    constructor
    · intro u hu0 hu1
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals simp [coFGM] <;> ring
    · intro u1 u2 v1 v2 hu1 hu2 hu3 hv1 hv2 hv3
      let a : ℝ := 1 - u1 - u2
      let b : ℝ := 1 - v1 - v2
      have ha : |a| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> dsimp [a] <;> linarith
      have hb : |b| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> dsimp [b] <;> linarith
      have ht : |theta| ≤ 1 := abs_le.mpr ⟨ht0, ht1⟩
      have hta : |theta| * |a| ≤ 1 := calc
        |theta| * |a| ≤ (1 : ℝ) * 1 :=
          mul_le_mul ht ha (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
      have htab : |theta * a * b| ≤ 1 := by
        rw [abs_mul, abs_mul]
        calc
          |theta| * |a| * |b| ≤ (1 : ℝ) * 1 :=
            mul_le_mul hta hb (abs_nonneg _) (by norm_num)
          _ = 1 := by ring
      have hfactor : 0 ≤ 1 + theta * a * b := by
        have hlow := (abs_le.mp htab).1
        linarith
      have heq : coRectangle (coFGM theta) u1 u2 v1 v2 =
          (u2-u1)*(v2-v1)*(1 + theta*a*b) := by
        unfold coRectangle coFGM
        dsimp [a, b]
        ring
      rw [heq]
      exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hu2) (sub_nonneg.mpr hv2)) hfactor
  refine ⟨hcop, ?_, ?_, ?_⟩
  · change coLower u v ≤ C u v
    have hc : coIsCopula C := hcop
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
  · change C u v ≤ coUpper u v
    have hc : coIsCopula C := hcop
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
  · unfold coTailJoint coFGM
    ring
