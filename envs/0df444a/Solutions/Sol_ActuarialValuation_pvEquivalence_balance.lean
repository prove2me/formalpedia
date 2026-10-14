-- Prove2me | solution 1 for ActuarialValuation.pvEquivalence_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:02:08.478975+00:00
-- url     : https://prove2.me/submissions/c49ade0b-0f17-4b0e-9fb1-af1a11caffdb

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvEquivalencePremium
import Definitions.Def_actuarial_pvExpected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p benefit annuity : Fin n → ℝ) (h : pvExpected p annuity ≠ 0) : pvEquivalencePremium p benefit annuity * pvExpected p annuity = pvExpected p benefit := by
  unfold pvEquivalencePremium
  exact div_mul_cancel₀ _ h
