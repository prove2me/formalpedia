-- Prove2me | solution 1 for ActuarialValuation.decrementCauseInnovation_other
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:35:36.32708+00:00
-- url     : https://prove2.me/submissions/715f98cc-6853-4a2f-8f18-d953898f4ea9

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
import Definitions.Def_actuarial_decrementTailMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) (c d : C) (h : d ≠ c) :
  decrementCauseInnovation w t c t d =
    -(w t c / decrementTailMass w t) := by
  classical
  simp [decrementCauseInnovation, h]
