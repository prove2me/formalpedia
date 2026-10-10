-- Prove2me | solution 1 for ActuarialValuation.decrementCauseInnovation_after
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:35:27.790418+00:00
-- url     : https://prove2.me/submissions/7476a297-6bd6-4a8f-b2b0-c1333f76b54d

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t k : ℕ) (c d : C)
  (h : k < t) : decrementCauseInnovation w t c k d = 0 := by
  classical
  have hneq : k ≠ t := by omega
  have hnot : ¬ t ≤ k := by omega
  simp [decrementCauseInnovation, hneq, hnot]
