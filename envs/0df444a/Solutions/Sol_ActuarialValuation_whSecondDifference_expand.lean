-- Prove2me | solution 1 for ActuarialValuation.whSecondDifference_expand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:31:24.690513+00:00
-- url     : https://prove2.me/submissions/70c3d75d-4066-469d-9b4d-23e823e5b350

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondDifference
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (i : ℕ) : whSecondDifference g i = g (i+2)-2*g (i+1)+g i := by
  simp only [whSecondDifference, whFirstDifference, Nat.add_assoc, Nat.reduceAdd]
  ring
