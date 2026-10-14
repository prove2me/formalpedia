-- Prove2me | solution 1 for ActuarialValuation.crRatingTwoStep_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:31:54.435348+00:00
-- url     : https://prove2.me/submissions/b410884e-16b0-4243-931f-2d77c98fc443

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
theorem solution (P : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (h : ∀ j, (∑ k : Fin 3, P j k)=1) : (∑ k : Fin 3, crRatingTwoStep P i k)=1 := by
  classical

  unfold crRatingTwoStep
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, h]
  simpa using h i

#print axioms solution
