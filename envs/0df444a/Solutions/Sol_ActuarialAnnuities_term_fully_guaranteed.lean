-- Prove2me | solution 1 for ActuarialAnnuities.term_fully_guaranteed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T06:02:45.997091+00:00
-- url     : https://prove2.me/submissions/73e5c885-85c3-4db0-8fc5-f37e619d24d3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bCertainPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ)
    (hg : n ≤ g) :
    bSurvivalPV h a n g delta v b p =
      bSurvival h p a * bCertainPV h a n delta v b := by
  classical
  unfold bSurvivalPV bCertainPV
  rw [mul_comm (bSurvival h p a), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hpmt : a ≤ j ∧ j < a + n
  · have hguar : j < a + g :=
      lt_of_lt_of_le hpmt.2 (Nat.add_le_add_left hg a)
    simp [hpmt, hguar, mul_comm, mul_left_comm, mul_assoc]
  · simp [hpmt]
