-- Prove2me | solution 1 for ActuarialValuation.decrementCauseInnovation_at
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:35:31.998562+00:00
-- url     : https://prove2.me/submissions/fbdf50b8-4400-4017-87ec-3b8a4ddd4fd8

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
import Definitions.Def_actuarial_decrementTailMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) (c : C) :
  decrementCauseInnovation w t c t c =
    1 - w t c / decrementTailMass w t := by
  classical
  simp [decrementCauseInnovation]
