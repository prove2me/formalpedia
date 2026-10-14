-- Prove2me | solution 1 for ActuarialValuation.crRatingExpectedPay_add
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:30:09.673492+00:00
-- url     : https://prove2.me/submissions/227b607e-b3ba-4783-9ec9-94acb02fa5dc

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
theorem solution (P : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (a b : Fin 3 → ℝ) : crRatingExpectedPay P i (fun j => a j+b j)=crRatingExpectedPay P i a+crRatingExpectedPay P i b := by
  classical

  simp [crRatingExpectedPay, mul_add, Finset.sum_add_distrib]

#print axioms solution
