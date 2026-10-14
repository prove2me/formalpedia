-- Prove2me | solution 1 for ActuarialValuation.crBondPrice_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:37:34.442383+00:00
-- url     : https://prove2.me/submissions/3cc6b5e9-d655-4b72-94c5-91d2c03d4a61

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
theorem solution {m : ℕ} (p : Fin m → ℝ) (assets : Fin m → ℝ) (debt discount : ℝ) (hp : ∀ i, 0≤p i) (ha : ∀ i, 0≤assets i) (hd : 0≤debt) (hdisc : 0≤discount) : 0≤crBondPrice p assets debt discount := by
  classical

  exact mul_nonneg hdisc (Finset.sum_nonneg (fun i hi => mul_nonneg (hp i) (le_min (ha i) hd)))

#print axioms solution
