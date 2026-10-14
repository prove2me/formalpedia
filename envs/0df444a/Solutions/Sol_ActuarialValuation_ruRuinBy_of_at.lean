-- Prove2me | solution 1 for ActuarialValuation.ruRuinBy_of_at
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:24:53.159141+00:00
-- url     : https://prove2.me/submissions/eb85346d-a3bc-4194-927b-613c3163f0cc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruRuinAt
import Definitions.Def_actuarial_ruRuinBy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c : ℝ) (x : ℕ → ℝ) (n : ℕ)
    (h : ruRuinAt u c x n) : ruRuinBy u c x n := by
  unfold ruRuinBy
  exact ⟨n, le_refl n, h⟩
