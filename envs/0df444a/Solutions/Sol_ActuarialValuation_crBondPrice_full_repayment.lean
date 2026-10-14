-- Prove2me | solution 1 for ActuarialValuation.crBondPrice_full_repayment
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:37:20.195009+00:00
-- url     : https://prove2.me/submissions/4b649f06-cee0-4ff2-bc7d-8fc9b917e39a

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
theorem solution {m : ℕ} (p : Fin m → ℝ) (assets : Fin m → ℝ) (debt discount : ℝ) (hsolvent : ∀ i, debt≤assets i) (hn : (∑ i : Fin m, p i)=1) : crBondPrice p assets debt discount=crRiskfreeBond debt discount := by
  classical

  unfold crBondPrice crExpectedDebt crDebtPayoff crRiskfreeBond
  simp_rw [min_eq_right (hsolvent _)]
  rw [← Finset.sum_mul, hn]
  ring

#print axioms solution
