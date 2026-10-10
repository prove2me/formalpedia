-- Prove2me | solution 1 for ActuarialValuation.cm1ReversionaryAnnuity_le_y
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:25:55.74693+00:00
-- url     : https://prove2.me/submissions/623613fb-e164-4e8b-867c-d0d67b90cbdb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SingleLifeAnnuity
import Definitions.Def_actuarial_cm1ReversionaryAnnuity
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (discount pY both : ℕ → ℝ) (n : ℕ) (hd : ∀ t ∈ Finset.range n, 0 ≤ discount t) (hb : ∀ t ∈ Finset.range n, 0 ≤ both t) : cm1ReversionaryAnnuity discount pY both n ≤ cm1SingleLifeAnnuity discount pY n := by
  unfold cm1ReversionaryAnnuity cm1SingleLifeAnnuity
  apply Finset.sum_le_sum
  intro t ht
  have h : 0 ≤ discount t * both t := mul_nonneg (hd t ht) (hb t ht)
  dsimp [cm1ReversionaryIndicator]
  nlinarith
