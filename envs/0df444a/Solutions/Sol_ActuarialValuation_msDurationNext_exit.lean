-- Prove2me | solution 1 for ActuarialValuation.msDurationNext_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:11:35.482441+00:00
-- url     : https://prove2.me/submissions/75e24414-485a-4100-94e7-de633888c0bf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msDurationNext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i j : Fin 3) (duration : ℕ) (h : i ≠ j) : msDurationNext i j duration = 0 := by
  simp [msDurationNext, h]
