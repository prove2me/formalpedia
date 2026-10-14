-- Prove2me | solution 1 for ActuarialValuation.crCreditRating_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:24:23.993021+00:00
-- url     : https://prove2.me/submissions/9909d36f-2737-4078-9708-1684e633cb20

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
theorem solution {m : ℕ} (p : Fin m → ℝ) (assets : Fin m → ℝ) (face discount : ℝ) (P : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (hp : ∀ j, 0≤p j) (hn : (∑ j : Fin m, p j)=1) (ha : ∀ j, 0≤assets j) (hf : 0≤face) (hd : 0≤discount) (hP : ∀ j, (∑ k : Fin 3, P j k)=1) : (crBondPrice p assets face discount≤crRiskfreeBond face discount) ∧ ((∑ k : Fin 3, crRatingTwoStep P i k)=1) ∧ (crCreditLossPV face discount (crBondPrice p assets face discount)≥0) := by
  classical

  have hb : crBondPrice p assets face discount ≤ crRiskfreeBond face discount := by
    have hdisc := hd
    let debt := face
    unfold crBondPrice crRiskfreeBond crExpectedDebt crDebtPayoff
    rw [mul_comm face discount]
    apply mul_le_mul_of_nonneg_left _ hdisc
    calc
      (∑ i : Fin m, p i * min (assets i) face) ≤ ∑ i : Fin m, p i * face :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (min_le_right _ _) (hp i))
      _ = face := by rw [← Finset.sum_mul, hn]; ring
  have hm : (∑ k : Fin 3, crRatingTwoStep P i k) = 1 := by
    unfold crRatingTwoStep
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hP]
    simpa using hP i
  exact ⟨hb, hm, sub_nonneg.mpr hb⟩

#print axioms solution
