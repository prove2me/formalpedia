-- Prove2me | solution 1 for ActuarialValuation.poissonThinnedRate_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:28:09.248755+00:00
-- url     : https://prove2.me/submissions/a7b11c56-048b-4647-8aef-25435510c5d7

import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_poissonThinnedRate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rate selection : ℝ) :
    poissonThinnedRate rate selection +
      poissonThinnedRate rate (1 - selection) = rate := by
  dsimp [poissonThinnedRate]
  ring
