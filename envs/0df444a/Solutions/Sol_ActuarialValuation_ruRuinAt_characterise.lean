-- Prove2me | solution 1 for ActuarialValuation.ruRuinAt_characterise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:27:17.523633+00:00
-- url     : https://prove2.me/submissions/bc4273f7-2f63-4d76-91a0-86129872857b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_ruRuinAt
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruClaimTotal
import Definitions.Def_actuarial_ruPremiumTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    ruRuinAt u c x n ↔
      ruClaimTotal x n > u+ruPremiumTotal c n := by
  unfold ruRuinAt ruPathSurplus
  constructor <;> intro h <;> linarith
