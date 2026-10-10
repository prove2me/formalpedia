-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonPredictiveVariance_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:41:40.573504+00:00
-- url     : https://prove2.me/submissions/0ebc951d-6e72-4f68-a1e9-af39d0631f5b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorMean
import Definitions.Def_actuarial_gammaPoissonPosteriorShape
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (a b e : ℝ) (c : ℕ)
  (ha : 0 < a) (hb : 0 < b) (he : 0 ≤ e) :
  gammaPoissonPosteriorMean a b e c ≤
    gammaPoissonPosteriorMean a b e c +
      gammaPoissonPosteriorShape a c /
        (gammaPoissonPosteriorRate b e) ^ 2 := by
  unfold gammaPoissonPosteriorMean gammaPoissonPosteriorShape
    gammaPoissonPosteriorRate
  apply le_add_of_nonneg_right
  exact div_nonneg (le_of_lt (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)))
    (sq_nonneg _)
