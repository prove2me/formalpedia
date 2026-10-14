-- Prove2me | solution 1 for ActuarialValuation.pvLoading_recover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:57:30.161419+00:00
-- url     : https://prove2.me/submissions/b990e1d8-1059-4e0f-8a54-db2fe32a7382

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvLoading
import Definitions.Def_actuarial_pvLoadedPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (equivalence loading : ℝ) : pvLoading (pvLoadedPremium equivalence loading) equivalence = loading := by
  unfold pvLoading pvLoadedPremium
  ring
