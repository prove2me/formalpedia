-- Prove2me | solution 1 for ActuarialValuation.crRatingTwoStep_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:34:03.439204+00:00
-- url     : https://prove2.me/submissions/8da45b6f-b3d8-4b1f-a647-2d8d2f782c3b

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
theorem solution (P : Fin 3 → Fin 3 → ℝ) (i k : Fin 3) (h : ∀ i j, 0≤P i j) : 0≤crRatingTwoStep P i k := by
  classical

  exact Finset.sum_nonneg (fun j hj => mul_nonneg (h i j) (h j k))

#print axioms solution
