-- Prove2me | solution 1 for ActuarialValuation.cm1AnnuityDue_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:14:39.459703+00:00
-- url     : https://prove2.me/submissions/c98828c0-b331-4585-ab26-bff782700b68

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1AnnuityDue
import Definitions.Def_actuarial_cm1Discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (n : ℕ) (hi : -1 < i) (hn : 0 < n) : 0 < cm1AnnuityDue i n := by
  unfold cm1AnnuityDue
  have hp : 0 < 1 + i := by linarith
  apply Finset.sum_pos
  · intro k hk
    simp only [cm1Discount, cm1Accum]
    exact one_div_pos.mpr (pow_pos hp k)
  · exact ⟨0, Finset.mem_range.mpr hn⟩
