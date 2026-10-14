-- Prove2me | solution 1 for ActuarialValuation.pvRiskPremium_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:12:25.809242+00:00
-- url     : https://prove2.me/submissions/b1bbac94-a5a8-48be-a805-87b5f476a574

import Theorems.Thm_ActuarialValuation_pvExpectedLoss_split
import Theorems.Thm_ActuarialValuation_pvEquivalence_balance
import Theorems.Thm_ActuarialValuation_pvAdequacy_loss_cdf
import Theorems.Thm_ActuarialValuation_pvAdequacy_mono_premium
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpectedLoss
import Definitions.Def_actuarial_pvEquivalencePremium
import Definitions.Def_actuarial_pvAdequacy
import Definitions.Def_actuarial_pvCdf
import Definitions.Def_actuarial_pvLoss
import Definitions.Def_actuarial_pvExpected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p benefit annuity : Fin n → ℝ) (P Q α : ℝ) (hmean : pvExpected p annuity ≠ 0) (hp : ∀ i, 0 ≤ p i) (hnorm : (∑ i : Fin n, p i) = 1) (ha : ∀ i, 0 ≤ annuity i) (hPQ : P ≤ Q) (hα : α ≤ pvAdequacy p benefit annuity P) : (pvExpectedLoss p benefit annuity (pvEquivalencePremium p benefit annuity) = 0) ∧ (pvAdequacy p benefit annuity P = pvCdf p (pvLoss benefit annuity P) 0) ∧ (α ≤ pvAdequacy p benefit annuity Q) := by
  refine ⟨?_, ?_, ?_⟩
  · have hbal :
        pvEquivalencePremium p benefit annuity * pvExpected p annuity =
          pvExpected p benefit :=
      ActuarialValuation.pvEquivalence_balance
        p benefit annuity hmean
    rw [ActuarialValuation.pvExpectedLoss_split]
    rw [← hbal]
    ring
  · exact ActuarialValuation.pvAdequacy_loss_cdf
      p benefit annuity P
  · exact le_trans hα
      (ActuarialValuation.pvAdequacy_mono_premium
        p benefit annuity P Q hPQ ha hp)
