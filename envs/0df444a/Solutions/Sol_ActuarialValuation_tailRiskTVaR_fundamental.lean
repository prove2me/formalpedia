-- Prove2me | solution 1 for ActuarialValuation.tailRiskTVaR_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:52:58.707987+00:00
-- url     : https://prove2.me/submissions/46974f4d-f8ab-4948-af3f-0d3b866b4481

import Mathlib
import Definitions.Def_actuarial_tailRiskAtomWeight
import Definitions.Def_actuarial_tailRiskStrictMass
import Definitions.Def_actuarial_tailRiskTVaR
import Definitions.Def_actuarial_tailRiskStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ)
  (hw : ∀ s, 0 ≤ w s) (ha : alpha < 1)
  (hbelow : tailRiskStrictMass w bound q ≤ 1 - alpha)
  (habove : 1 - alpha ≤ tailRiskStrictMass w bound q + w q) :
  (0 ≤ tailRiskAtomWeight w bound q alpha ∧
    tailRiskAtomWeight w bound q alpha ≤ w q) ∧
  (tailRiskTVaR w bound q alpha =
    (q : ℝ) + tailRiskStopLoss w bound q / (1 - alpha)) ∧
  ((q : ℝ) ≤ tailRiskTVaR w bound q alpha) := by
  have hnonneg : 0 ≤ tailRiskAtomWeight w bound q alpha := by
    unfold tailRiskAtomWeight
    linarith
  have hle : tailRiskAtomWeight w bound q alpha ≤ w q := by
    unfold tailRiskAtomWeight
    linarith
  have hstop : 0 ≤ tailRiskStopLoss w bound q := by
    unfold tailRiskStopLoss
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (Nat.cast_nonneg _) (hw s)
  have hsel : tailRiskSelectedLoss w bound q alpha =
      (q : ℝ) * (1 - alpha) + tailRiskStopLoss w bound q := by
    have key :
        (∑ s ∈ Finset.range (bound + 1),
          if q < s then (s : ℝ) * w s else 0) =
        tailRiskStopLoss w bound q +
          (q : ℝ) * tailRiskStrictMass w bound q := by
      unfold tailRiskStopLoss tailRiskStrictMass
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases h : q < s
      · simp only [if_pos h]
        have hnat : s - q + q = s :=
          Nat.sub_add_cancel (Nat.le_of_lt h)
        have hr : ((s - q : ℕ) : ℝ) + (q : ℝ) = (s : ℝ) := by
          exact_mod_cast hnat
        calc
          (s : ℝ) * w s =
              (((s - q : ℕ) : ℝ) + (q : ℝ)) * w s := by rw [hr]
          _ = ((s - q : ℕ) : ℝ) * w s + (q : ℝ) * w s := by ring
      · have hq : s ≤ q := le_of_not_gt h
        simp [h, Nat.sub_eq_zero_of_le hq]
    unfold tailRiskSelectedLoss tailRiskAtomWeight
    rw [key]
    ring
  have hdenpos : 0 < 1 - alpha := by linarith
  have hden : 1 - alpha ≠ 0 := ne_of_gt hdenpos
  have hrep : tailRiskTVaR w bound q alpha =
      (q : ℝ) + tailRiskStopLoss w bound q / (1 - alpha) := by
    unfold tailRiskTVaR
    rw [hsel]
    field_simp [hden]
  have hratio : 0 ≤ tailRiskStopLoss w bound q / (1 - alpha) :=
    div_nonneg hstop (le_of_lt hdenpos)
  have hge : (q : ℝ) ≤ tailRiskTVaR w bound q alpha := by
    rw [hrep]
    linarith
  exact ⟨⟨hnonneg, hle⟩, hrep, hge⟩
