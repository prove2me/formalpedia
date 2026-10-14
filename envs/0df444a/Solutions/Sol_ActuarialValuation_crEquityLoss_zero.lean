-- Prove2me | solution 1 for ActuarialValuation.crEquityLoss_zero
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:42:32.834834+00:00
-- url     : https://prove2.me/submissions/030552b1-cc95-41d2-aa6d-efd9fd453d48

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
theorem solution (assets debt : ℝ) (h : debt≤assets) : crEquityLoss assets debt=0 := by
  classical

  simp [crEquityLoss, crDebtPayoff, min_eq_right h]

#print axioms solution
