-- Prove2me | solution 1 for ActuarialValuation.gamblerFairSuccess_target
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:45:42.044982+00:00
-- url     : https://prove2.me/submissions/662764da-97fa-499b-895c-2266c05488d5

import Definitions.Def_actuarial_gamblerFairSuccess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N : ℕ) (hN : 0 < N) :
    gamblerFairSuccess N N = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp [gamblerFairSuccess, hn]
