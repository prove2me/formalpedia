-- Prove2me | solution 1 for ActuarialValuation.crBondPrice_le_riskfree
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:38:26.184308+00:00
-- url     : https://prove2.me/submissions/6143d6fc-59db-4d0e-a601-d7add10d7666

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
theorem solution {m : ℕ} (p : Fin m → ℝ) (assets : Fin m → ℝ) (debt discount : ℝ) (hp : ∀ i, 0≤p i) (hn : (∑ i : Fin m, p i)=1) (hdisc : 0≤discount) : crBondPrice p assets debt discount≤crRiskfreeBond debt discount := by
  classical

  unfold crBondPrice crRiskfreeBond crExpectedDebt crDebtPayoff
  rw [mul_comm debt discount]
  apply mul_le_mul_of_nonneg_left _ hdisc
  calc
    (∑ i : Fin m, p i * min (assets i) debt) ≤ ∑ i : Fin m, p i * debt :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (min_le_right _ _) (hp i))
    _ = debt := by rw [← Finset.sum_mul, hn]; ring

#print axioms solution
