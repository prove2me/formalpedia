-- Prove2me | solution 1 for ActuarialValuation.crRatingExpectedPay_constant
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:28:40.761709+00:00
-- url     : https://prove2.me/submissions/7d30068f-d70d-4ac6-bfb2-28012ab6f5c5

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
theorem solution (P : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (c : ℝ) (h : (∑ j : Fin 3, P i j)=1) : crRatingExpectedPay P i (fun _ => c)=c := by
  classical

  unfold crRatingExpectedPay
  rw [← Finset.sum_mul, h]
  ring

#print axioms solution
