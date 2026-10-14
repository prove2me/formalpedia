-- Prove2me | solution 1 for ActuarialValuation.crCreditSpread_zero
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:34:17.559883+00:00
-- url     : https://prove2.me/submissions/bd75e238-42c4-4c2b-80bf-fb9444854757

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
theorem solution (face price term : ℝ) : crCreditSpread face price price term=0 := by
  classical

  simp [crCreditSpread]

#print axioms solution
