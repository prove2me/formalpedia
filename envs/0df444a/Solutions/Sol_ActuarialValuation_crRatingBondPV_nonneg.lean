-- Prove2me | solution 1 for ActuarialValuation.crRatingBondPV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:27:36.952654+00:00
-- url     : https://prove2.me/submissions/22552ac6-32cd-4bce-9709-7c6fd8e79603

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
theorem solution (P : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (cash : Fin 3 → ℝ) (discount : ℝ) (hP : ∀ j, 0≤P i j) (hc : ∀ j, 0≤cash j) (hd : 0≤discount) : 0≤crRatingBondPV P i cash discount := by
  classical

  exact mul_nonneg hd (Finset.sum_nonneg (fun j hj => mul_nonneg (hP j) (hc j)))

#print axioms solution
