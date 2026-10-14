-- Prove2me | solution 1 for ActuarialValuation.ruFirstRuin_by
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:25:12.469726+00:00
-- url     : https://prove2.me/submissions/bc47a496-1c5e-427b-b423-64b149c0926e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruFirstRuin
import Definitions.Def_actuarial_ruRuinAt
import Definitions.Def_actuarial_ruRuinBy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c : ℝ) (x : ℕ → ℝ) (n : ℕ)
    (h : ruFirstRuin u c x n) : ruRuinBy u c x n := by
  unfold ruRuinBy
  exact ⟨n, le_refl n, h.1⟩
