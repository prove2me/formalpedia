-- Prove2me | solution 1 for ActuarialValuation.ratClassIndicated_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:17:54.365625+00:00
-- url     : https://prove2.me/submissions/21aa7970-ae3d-4d5b-be90-66c964e67cf2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClassIndicated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (freq severity : ℝ) (hf : 0 ≤ freq) (hs : 0 ≤ severity) :
    0 ≤ ratClassIndicated freq severity := by
  unfold ratClassIndicated
  exact mul_nonneg hf hs
