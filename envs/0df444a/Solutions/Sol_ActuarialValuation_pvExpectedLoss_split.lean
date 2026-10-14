-- Prove2me | solution 1 for ActuarialValuation.pvExpectedLoss_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:08:10.308671+00:00
-- url     : https://prove2.me/submissions/82492dfe-5cb5-4d08-8912-f7cf44531266

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpectedLoss
import Definitions.Def_actuarial_pvExpected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p benefit annuity : Fin n → ℝ) (premium : ℝ) : pvExpectedLoss p benefit annuity premium = pvExpected p benefit - premium * pvExpected p annuity := by
  unfold pvExpectedLoss pvExpected pvLoss pvPremium
  calc
    (∑ i : Fin n, p i * (benefit i - premium * annuity i)) =
        (∑ i : Fin n, p i * benefit i) -
          ∑ i : Fin n, premium * (p i * annuity i) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i : Fin n, p i * benefit i) -
        premium * (∑ i : Fin n, p i * annuity i) := by
      rw [Finset.mul_sum]
