-- Prove2me | solution 1 for ActuarialValuation.tailExcess_mono_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:30:07.934057+00:00
-- url     : https://prove2.me/submissions/12a55e2b-612f-42e9-a975-c172e4b1ae93

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailExcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x y t : ℝ) (h : x ≤ y) :
    tailExcess x t ≤ tailExcess y t := by
  unfold tailExcess
  refine max_le_max ?_ le_rfl
  exact sub_le_sub_right h t
