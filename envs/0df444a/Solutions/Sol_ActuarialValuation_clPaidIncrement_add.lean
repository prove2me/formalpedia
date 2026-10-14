-- Prove2me | solution 1 for ActuarialValuation.clPaidIncrement_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:26.208041+00:00
-- url     : https://prove2.me/submissions/cb70667c-9e1c-4824-95e3-b2f48a9f208d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clPaidIncrement
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p q : ℕ → ℕ → ℝ) (i j : ℕ) : clPaidIncrement (fun x y => p x y + q x y) i j = clPaidIncrement p i j + clPaidIncrement q i j := by
  simp only [clPaidIncrement]
  ring
