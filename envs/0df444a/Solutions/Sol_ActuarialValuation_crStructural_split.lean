-- Prove2me | solution 1 for ActuarialValuation.crStructural_split
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:44:18.226285+00:00
-- url     : https://prove2.me/submissions/c41cda17-b081-49a3-9247-373a41f12f2c

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
theorem solution (assets debt : ℝ) (h : 0≤assets) (hd : 0≤debt) : crEquityPayoff assets debt+crDebtPayoff assets debt=assets := by
  classical

  unfold crEquityPayoff crDebtPayoff
  by_cases he : assets ≤ debt
  · rw [max_eq_left (sub_nonpos.mpr he), min_eq_left he]; ring
  · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge he)), min_eq_right (le_of_not_ge he)]; ring

#print axioms solution
