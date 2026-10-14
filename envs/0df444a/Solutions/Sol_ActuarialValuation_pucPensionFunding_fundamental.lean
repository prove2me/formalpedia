-- Prove2me | solution 1 for ActuarialValuation.pucPensionFunding_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:35:20.44645+00:00
-- url     : https://prove2.me/submissions/d59d4efe-311c-43ef-9b59-489af31d9b2c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_pucActuarialLiability
import Definitions.Def_actuarial_pucFutureNormalCost
import Definitions.Def_actuarial_pucProjectedBenefitPV
import Definitions.Def_actuarial_pucUnfundedLiability
import Definitions.Def_actuarial_pucAmortisationRate
import Definitions.Def_actuarial_pucFundingSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (unit : ℕ → ℝ) (n m : ℕ) (f assets payrollPV : ℝ) (hF : 0 < payrollPV) (hUL : 0 ≤ pucUnfundedLiability (pucActuarialLiability unit n f) assets) : (pucProjectedBenefitPV unit n m f = pucActuarialLiability unit n f + pucFutureNormalCost unit n m f) ∧ (0 ≤ pucAmortisationRate (pucUnfundedLiability (pucActuarialLiability unit n f) assets) payrollPV) ∧ (pucFundingSurplus assets (pucAmortisationRate (pucUnfundedLiability (pucActuarialLiability unit n f) assets) payrollPV) payrollPV (pucActuarialLiability unit n f) = 0) ∧ (∀ c : ℝ, pucAmortisationRate (pucUnfundedLiability (pucActuarialLiability unit n f) assets) payrollPV ≤ c → 0 ≤ pucFundingSurplus assets c payrollPV (pucActuarialLiability unit n f)) := by
  have hpay : payrollPV ≠ 0 := ne_of_gt hF
  have hpart :
      pucProjectedBenefitPV unit n m f =
        pucActuarialLiability unit n f + pucFutureNormalCost unit n m f := by
    simp only [pucProjectedBenefitPV, pucTotalBenefit,
      pucActuarialLiability, pucFutureNormalCost, add_mul]
  have hrate :
      0 ≤ pucAmortisationRate
        (pucUnfundedLiability (pucActuarialLiability unit n f) assets)
        payrollPV := by
    unfold pucAmortisationRate
    exact div_nonneg hUL (le_of_lt hF)
  have hzero :
      pucFundingSurplus assets
        (pucAmortisationRate
          (pucUnfundedLiability (pucActuarialLiability unit n f) assets)
          payrollPV)
        payrollPV (pucActuarialLiability unit n f) = 0 := by
    unfold pucFundingSurplus pucAmortisationRate pucUnfundedLiability
    field_simp [hpay] <;> ring
  have habove :
      ∀ c : ℝ,
        pucAmortisationRate
          (pucUnfundedLiability (pucActuarialLiability unit n f) assets)
          payrollPV ≤ c →
          0 ≤ pucFundingSurplus assets c payrollPV
            (pucActuarialLiability unit n f) := by
    intro c hc
    unfold pucAmortisationRate pucUnfundedLiability at hc
    unfold pucFundingSurplus
    have hmul := mul_le_mul_of_nonneg_right hc (le_of_lt hF)
    have hcancel :
        ((pucActuarialLiability unit n f - assets) / payrollPV) * payrollPV =
          pucActuarialLiability unit n f - assets := by
      field_simp [hpay] <;> ring
    rw [hcancel] at hmul
    linarith
  exact ⟨hpart, hrate, hzero, habove⟩
