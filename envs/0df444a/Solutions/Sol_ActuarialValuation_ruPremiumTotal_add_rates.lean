-- Prove2me | solution 1 for ActuarialValuation.ruPremiumTotal_add_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:15:09.751369+00:00
-- url     : https://prove2.me/submissions/c7dca75b-d238-4c65-8378-e801a6e472fc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ruPremiumTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b : ℝ) (n : ℕ) :
    ruPremiumTotal (a+b) n = ruPremiumTotal a n + ruPremiumTotal b n := by
  unfold ruPremiumTotal
  ring
