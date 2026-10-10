-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonExperienceWeight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:50:28.505038+00:00
-- url     : https://prove2.me/submissions/9b51d293-21b8-4a1c-976c-4bc137f72105

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonExperienceWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (b e : ℝ) (hb : 0 < b) (he : 0 ≤ e) :
  gammaPoissonExperienceWeight b e ≤ 1 := by
  change e / (b + e) ≤ 1
  have hd : 0 < b + e := add_pos_of_pos_of_nonneg hb he
  apply (div_le_iff₀ hd).2
  simpa only [one_mul] using
    (show e ≤ b + e from le_add_of_nonneg_left (le_of_lt hb))
