-- Prove2me | solution 1 for ActuarialValuation.crRecoveryPayoff_le_face
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:24:24.998526+00:00
-- url     : https://prove2.me/submissions/278e59b2-1046-433e-9dcb-fd50813cd40a

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
theorem solution (face rate : ℝ) (hf : 0≤face) (hr0 : 0≤rate) (hr1 : rate≤1) : crRecoveryPayoff face rate≤face := by
  classical

  unfold crRecoveryPayoff
  nlinarith

#print axioms solution
