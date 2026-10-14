-- Prove2me | solution 1 for ActuarialValuation.lcRateRatio_compose
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:31:39.485829+00:00
-- url     : https://prove2.me/submissions/4b6b5e74-bfbb-4120-93af-6a8dc1e05202

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_lcRateRatio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b k1 k2 k3 : ℝ) :
    lcRateRatio b k1 k3 =
      lcRateRatio b k1 k2 * lcRateRatio b k2 k3 := by
  simp only [lcRateRatio, lcLogChange]
  rw [← Real.exp_add]
  congr 1
  ring
