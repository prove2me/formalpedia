-- Prove2me | solution 1 for ActuarialValuation.msDurationNext_stay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:11:23.042257+00:00
-- url     : https://prove2.me/submissions/dd76652a-5659-48f7-8b39-580671bdc0a2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msDurationNext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : Fin 3) (duration : ℕ) : msDurationNext i i duration = duration+1 := by
  simp [msDurationNext]
