-- Prove2me | solution 1 for ActuarialValuation.crExpectedAssets_split
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:39:55.798918+00:00
-- url     : https://prove2.me/submissions/d3d8ed8c-88f2-4f0f-a871-d4cfe8bcacdf

import Mathlib
import Definitions.Def_actuarial_crBondPrice
import Definitions.Def_actuarial_crBondYield
import Definitions.Def_actuarial_crCreditLossPV
import Definitions.Def_actuarial_crCreditSpread
import Definitions.Def_actuarial_crDebtPayoff
import Definitions.Def_actuarial_crDefault
import Definitions.Def_actuarial_crEquityLoss
import Definitions.Def_actuarial_crEquityPayoff
import Definitions.Def_actuarial_crExpectedDebt
import Definitions.Def_actuarial_crExpectedEquity
import Definitions.Def_actuarial_crRatingBondPV
import Definitions.Def_actuarial_crRatingExpectedPay
import Definitions.Def_actuarial_crRatingTwoStep
import Definitions.Def_actuarial_crRecoveryPayoff
import Definitions.Def_actuarial_crRiskfreeBond
set_option autoImplicit false
noncomputable section
open ActuarialValuation
theorem solution {m : ℕ} (p : Fin m → ℝ) (assets : Fin m → ℝ) (debt : ℝ) (ha : ∀ i, 0≤assets i) (hd : 0≤debt) : crExpectedDebt p assets debt+crExpectedEquity p assets debt=∑ i : Fin m, p i*assets i := by
  classical

  unfold crExpectedDebt crExpectedEquity crDebtPayoff crEquityPayoff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : assets i ≤ debt
  · rw [min_eq_left h, max_eq_left (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_right (sub_nonneg.mpr (le_of_not_ge h))]
    ring

#print axioms solution
