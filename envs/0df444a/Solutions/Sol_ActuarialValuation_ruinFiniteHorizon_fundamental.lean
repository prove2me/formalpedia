-- Prove2me | solution 1 for ActuarialValuation.ruinFiniteHorizon_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:09:17.225147+00:00
-- url     : https://prove2.me/submissions/9dd6db76-042b-46bb-9e18-5714a4aa146c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite
import Definitions.Def_actuarial_ruinClaimMass
import Definitions.Def_actuarial_ruinAdjustmentMoment
import Definitions.Def_actuarial_ruinExponentialBound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B c n : ℕ) (u : ℤ) (R : ℝ)
  (hw : ∀ k, 0 ≤ w k)
  (hmass : ruinClaimMass w B = 1)
  (hR : 0 ≤ R)
  (hmoment : ruinAdjustmentMoment w B c R ≤ 1) :
  (0 ≤ ruinProbabilityFinite w B c n u ∧
    ruinProbabilityFinite w B c n u ≤ 1) ∧
  (ruinProbabilityFinite w B c n u ≤
    ruinExponentialBound R u) := by
  have hnonneg : ∀ m v, 0 ≤ ruinProbabilityFinite w B c m v := by
    intro m
    induction m with
    | zero =>
        intro v
        by_cases hv : v < 0 <;> simp [ruinProbabilityFinite, hv]
    | succ m ih =>
        intro v
        by_cases hv : v < 0
        · simp [ruinProbabilityFinite, hv]
        · simp only [ruinProbabilityFinite, if_neg hv]
          apply Finset.sum_nonneg
          intro k hk
          exact mul_nonneg (hw k) (ih (ruinNextSurplus v c k))
  have hunit : ∀ m v, ruinProbabilityFinite w B c m v ≤ 1 := by
    intro m
    induction m with
    | zero =>
        intro v
        by_cases hv : v < 0 <;> simp [ruinProbabilityFinite, hv]
    | succ m ih =>
        intro v
        by_cases hv : v < 0
        · simp [ruinProbabilityFinite, hv]
        · simp only [ruinProbabilityFinite, if_neg hv]
          calc
            (∑ k ∈ Finset.range (B + 1),
                w k * ruinProbabilityFinite w B c m
                  (ruinNextSurplus v c k))
                ≤ ∑ k ∈ Finset.range (B + 1), w k := by
                  apply Finset.sum_le_sum
                  intro k hk
                  simpa using mul_le_mul_of_nonneg_left
                    (ih (ruinNextSurplus v c k)) (hw k)
            _ = 1 := by simpa [ruinClaimMass] using hmass
  have htransition (v : ℤ) (k : ℕ) :
      ruinExponentialBound R (ruinNextSurplus v c k) =
        ruinExponentialBound R v * Real.exp (R * ((k : ℝ) - (c : ℝ))) := by
    unfold ruinExponentialBound ruinNextSurplus
    push_cast
    rw [← Real.exp_add]
    congr 1
    ring
  have hweighted (v : ℤ) :
      (∑ k ∈ Finset.range (B + 1),
        w k * ruinExponentialBound R (ruinNextSurplus v c k)) =
        ruinExponentialBound R v * ruinAdjustmentMoment w B c R := by
    calc
      _ = ∑ k ∈ Finset.range (B + 1),
            ruinExponentialBound R v *
              (w k * Real.exp (R * ((k : ℝ) - (c : ℝ)))) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [htransition v k]
            ring
      _ = ruinExponentialBound R v *
            ∑ k ∈ Finset.range (B + 1),
              w k * Real.exp (R * ((k : ℝ) - (c : ℝ))) := by
            rw [← Finset.mul_sum]
      _ = _ := rfl
  have hlundberg : ∀ m v,
      ruinProbabilityFinite w B c m v ≤ ruinExponentialBound R v := by
    intro m
    induction m with
    | zero =>
        intro v
        by_cases hv : v < 0
        · simp only [ruinProbabilityFinite, if_pos hv]
          unfold ruinExponentialBound
          apply Real.one_le_exp_iff.mpr
          apply neg_nonneg.mpr
          exact mul_nonpos_of_nonneg_of_nonpos hR
            (by exact_mod_cast le_of_lt hv)
        · simp only [ruinProbabilityFinite, if_neg hv]
          exact le_of_lt (Real.exp_pos _)
    | succ m ih =>
        intro v
        by_cases hv : v < 0
        · simp only [ruinProbabilityFinite, if_pos hv]
          unfold ruinExponentialBound
          apply Real.one_le_exp_iff.mpr
          apply neg_nonneg.mpr
          exact mul_nonpos_of_nonneg_of_nonpos hR
            (by exact_mod_cast le_of_lt hv)
        · simp only [ruinProbabilityFinite, if_neg hv]
          calc
            (∑ k ∈ Finset.range (B + 1),
                w k * ruinProbabilityFinite w B c m
                  (ruinNextSurplus v c k))
                ≤ ∑ k ∈ Finset.range (B + 1),
                    w k * ruinExponentialBound R (ruinNextSurplus v c k) := by
                  apply Finset.sum_le_sum
                  intro k hk
                  exact mul_le_mul_of_nonneg_left
                    (ih (ruinNextSurplus v c k)) (hw k)
            _ = ruinExponentialBound R v * ruinAdjustmentMoment w B c R :=
                  hweighted v
            _ ≤ ruinExponentialBound R v * 1 := by
                  apply mul_le_mul_of_nonneg_left hmoment
                  exact le_of_lt (Real.exp_pos _)
            _ = ruinExponentialBound R v := by simp
  exact ⟨⟨hnonneg n u, hunit n u⟩, hlundberg n u⟩
