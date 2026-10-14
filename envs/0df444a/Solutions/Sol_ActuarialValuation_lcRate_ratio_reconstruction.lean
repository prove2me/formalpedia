-- Prove2me | solution 1 for ActuarialValuation.lcRate_ratio_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:38:23.079393+00:00
-- url     : https://prove2.me/submissions/73a45264-9002-4a44-95d1-ebeca21e9ce3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_lcRate
import Definitions.Def_actuarial_lcRateRatio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b k1 k2 : ℝ) :
    lcRate a b k2 = lcRate a b k1 * lcRateRatio b k1 k2 := by
  simp only [lcRate, lcLogRate, lcRateRatio, lcLogChange]
  rw [← Real.exp_add]
  congr 1
  ring
