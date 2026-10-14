-- Prove2me | solution 1 for ActuarialValuation.crCreditSpread_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:35:09.343453+00:00
-- url     : https://prove2.me/submissions/b0da3d0c-5524-40e4-bf2b-5dfd6d209d80

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
theorem solution (face riskfree risky term : ℝ) (hface : 0<face) (hriskfree : 0<riskfree) (hrisky : 0<risky) (hterm : 0<term) (h : risky≤riskfree) : 0≤crCreditSpread face riskfree risky term := by
  classical

  unfold crCreditSpread crBondYield
  apply sub_nonneg.mpr
  apply div_le_div_of_nonneg_right _ hterm.le
  apply Real.log_le_log (div_pos hface hriskfree)
  exact div_le_div_of_nonneg_left hface.le hrisky h

#print axioms solution
