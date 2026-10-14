-- Prove2me | solution 1 for ActuarialValuation.coFGM_is_copula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:29:30.708251+00:00
-- url     : https://prove2.me/submissions/c305d06f-1dd1-4a4d-baa9-09dfd8e70fe5

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coFGM
import Definitions.Def_actuarial_coIsCopula

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (theta : ℝ) (hl : -1≤theta) (hu : theta≤1) : coIsCopula (coFGM theta) := by
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
    have ht : |theta| ≤ 1 := abs_le.mpr ⟨hl, hu⟩
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
