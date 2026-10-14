-- Prove2me | solution 1 for ActuarialValuation.ulAccountPath_zero_noperiod
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:01:22.1556+00:00
-- url     : https://prove2.me/submissions/ae4b11d1-ed23-4bf6-8638-da8783c1094a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAccountPath

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (initial : ℝ) (n : ℕ) : ulAccountPath initial (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) n = initial := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ulTypeBNext
        (ulAccountPath initial (fun _ => 0) (fun _ => 0) (fun _ => 0)
          (fun _ => 0) (fun _ => 0) (fun _ => 0) n)
        0 0 0 0 0 0 = initial
      rw [ih]
      simp [ulTypeBNext, ulEarned, ulAfterPremium, ulAllocatedPremium]
