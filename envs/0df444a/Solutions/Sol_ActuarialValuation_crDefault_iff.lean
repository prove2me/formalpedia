-- Prove2me | solution 1 for ActuarialValuation.crDefault_iff
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:41:40.879786+00:00
-- url     : https://prove2.me/submissions/2d5d8da5-693e-4838-820c-386d62681ded

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
theorem solution (assets debt : ℝ) : crDefault assets debt ↔ crEquityPayoff assets debt=0 ∧ assets≠debt := by
  classical

  simp only [crDefault, crEquityPayoff, max_eq_left_iff, sub_nonpos]
  constructor
  · intro h
    exact ⟨h.le, ne_of_lt h⟩
  · rintro ⟨h, hn⟩
    exact lt_of_le_of_ne h hn

#print axioms solution
