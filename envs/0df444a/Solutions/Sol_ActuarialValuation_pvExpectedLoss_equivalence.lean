-- Prove2me | solution 1 for ActuarialValuation.pvExpectedLoss_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:10:09.050044+00:00
-- url     : https://prove2.me/submissions/f9500675-943d-42d8-a873-3a795586dae3

import Mathlib.Tactic.Ring
import Theorems.Thm_ActuarialValuation_pvExpectedLoss_split
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpectedLoss
import Definitions.Def_actuarial_pvEquivalencePremium
import Definitions.Def_actuarial_pvExpected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p benefit annuity : Fin n → ℝ) (h : pvExpected p annuity ≠ 0) : pvExpectedLoss p benefit annuity (pvEquivalencePremium p benefit annuity) = 0 := by
  rw [ActuarialValuation.pvExpectedLoss_split]
  unfold pvEquivalencePremium
  rw [div_mul_cancel₀ _ h]
  ring
