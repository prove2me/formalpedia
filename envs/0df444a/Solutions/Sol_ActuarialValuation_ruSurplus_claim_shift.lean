-- Prove2me | solution 1 for ActuarialValuation.ruSurplus_claim_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:28:22.045451+00:00
-- url     : https://prove2.me/submissions/c281a23d-9264-4757-8fe4-9338637c2fca

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruClaimTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c : ℝ) (x y : ℕ → ℝ) (n : ℕ) :
    ruPathSurplus u c (fun k => x k+y k) n =
      ruPathSurplus u c x n - ruClaimTotal y n := by
  unfold ruPathSurplus ruClaimTotal
  simp only [Finset.sum_add_distrib]
  ring
