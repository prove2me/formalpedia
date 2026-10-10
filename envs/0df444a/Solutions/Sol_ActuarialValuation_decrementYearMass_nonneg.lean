-- Prove2me | solution 1 for ActuarialValuation.decrementYearMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T14:50:11.163979+00:00
-- url     : https://prove2.me/submissions/b5289a6b-4c34-455e-9679-82580398095e

import Mathlib
import Definitions.Def_actuarial_decrementYearMass
open ActuarialValuation

theorem solution {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) (hw : ∀ c, 0 ≤ w t c) :
  0 ≤ decrementYearMass w t := by
  unfold decrementYearMass
  exact Finset.sum_nonneg fun c _ => hw c
