-- Prove2me | solution 1 for ActuarialValuation.credibilityPremium_translation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:42:24.503262+00:00
-- url     : https://prove2.me/submissions/be66d174-2f4a-45d6-a86e-9ab3f2b39a40

import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_credibilityPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (mu observed z shift : ℝ) :
  credibilityPremium (mu + shift) (observed + shift) z =
    credibilityPremium mu observed z + shift := by
  unfold credibilityPremium
  ring
