-- Prove2me | solution 1 for ActuarialValuation.decrementAnnualRisk_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:39:06.167896+00:00
-- url     : https://prove2.me/submissions/354aef71-2f8f-4014-a90b-24d0d394189b

import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_actuarial_decrementAnnualRisk
import Definitions.Def_actuarial_decrementYearMass
import Definitions.Def_actuarial_decrementTailMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {C : Type*} [Fintype C]
  (w rho : ℕ → C → ℝ) (t : ℕ)
  (hw : ∀ c, 0 ≤ w t c)
  (hS : 0 < decrementTailMass w t)
  (hD : decrementYearMass w t ≤ decrementTailMass w t) :
  0 ≤ decrementAnnualRisk w rho t := by
  let f : C → ℝ := fun c => Real.sqrt (w t c)
  let g : C → ℝ := fun c => f c * rho t c
  have hf (c : C) : (f c) ^ 2 = w t c := by
    dsimp [f]
    exact Real.sq_sqrt (hw c)
  have hfg : (∑ c : C, f c * g c) =
      (∑ c : C, w t c * rho t c) := by
    apply Finset.sum_congr rfl
    intro c _
    calc
      f c * g c = (f c) ^ 2 * rho t c := by dsimp [g]; ring
      _ = w t c * rho t c := by rw [hf c]
  have hff : (∑ c : C, (f c) ^ 2) = decrementYearMass w t := by
    unfold decrementYearMass
    apply Finset.sum_congr rfl
    intro c _
    exact hf c
  have hgg : (∑ c : C, (g c) ^ 2) =
      (∑ c : C, w t c * (rho t c) ^ 2) := by
    apply Finset.sum_congr rfl
    intro c _
    calc
      (g c) ^ 2 = (f c) ^ 2 * (rho t c) ^ 2 := by dsimp [g]; ring
      _ = w t c * (rho t c) ^ 2 := by rw [hf c]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset C) f g
  rw [hfg, hff, hgg] at hcs
  have hA : 0 ≤ (∑ c : C, w t c * (rho t c) ^ 2) := by
    apply Finset.sum_nonneg
    intro c _
    exact mul_nonneg (hw c) (sq_nonneg _)
  have hle : decrementYearMass w t *
      (∑ c : C, w t c * (rho t c) ^ 2) ≤
      decrementTailMass w t *
      (∑ c : C, w t c * (rho t c) ^ 2) :=
    mul_le_mul_of_nonneg_right hD hA
  have htotal := le_trans hcs hle
  unfold decrementAnnualRisk
  have hnz : decrementTailMass w t ≠ 0 := ne_of_gt hS
  apply sub_nonneg.mpr
  exact (div_le_iff₀ hS).2 (by nlinarith [htotal])
