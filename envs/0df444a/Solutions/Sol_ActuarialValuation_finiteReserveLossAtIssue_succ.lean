-- Prove2me | solution 1 for ActuarialValuation.finiteReserveLossAtIssue_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:25:04.488417+00:00
-- url     : https://prove2.me/submissions/1c187b7e-db05-443c-8f09-1030026df789

import Mathlib
import Definitions.Def_actuarial_finiteLifeDeathIndicator
import Definitions.Def_actuarial_finiteLifeInForceIndicator
import Definitions.Def_actuarial_finiteReserveLossAtIssue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (K n : ℕ) (v : ℝ) (premium benefit reserve : ℕ → ℝ) :
    finiteReserveLossAtIssue K (n + 1) v premium benefit reserve =
      finiteReserveLossAtIssue K n v premium benefit reserve +
      v ^ (n + 1) * benefit (n + 1) * finiteLifeDeathIndicator K n -
      v ^ n * premium n * finiteLifeInForceIndicator K n +
      v ^ (n + 1) * reserve (n + 1) * finiteLifeInForceIndicator K (n + 1) -
      v ^ n * reserve n * finiteLifeInForceIndicator K n := by
  simp only [finiteReserveLossAtIssue, Finset.sum_range_succ]
  ring
