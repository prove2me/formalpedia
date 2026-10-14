-- Prove2me | solution 1 for ActuarialValuation.tailExcess_antitone_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:31:10.548385+00:00
-- url     : https://prove2.me/submissions/ed157f9c-2237-467f-b60d-31ab4134860d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailExcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x t u : ℝ) (h : t ≤ u) :
    tailExcess x u ≤ tailExcess x t := by
  unfold tailExcess
  refine max_le_max ?_ le_rfl
  exact sub_le_sub_left h x
