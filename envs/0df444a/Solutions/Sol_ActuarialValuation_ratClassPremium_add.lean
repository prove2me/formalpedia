-- Prove2me | solution 1 for ActuarialValuation.ratClassPremium_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:19:54.491669+00:00
-- url     : https://prove2.me/submissions/a5b8e1c2-7b89-4266-89c8-b06a5573296b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClassPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e1 e2 base rel : ℝ) : ratClassPremium (e1+e2) base rel = ratClassPremium e1 base rel + ratClassPremium e2 base rel := by
  simp [ratClassPremium, add_mul]
