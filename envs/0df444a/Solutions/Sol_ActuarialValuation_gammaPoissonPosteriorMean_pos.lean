-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonPosteriorMean_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:40:31.646323+00:00
-- url     : https://prove2.me/submissions/114d5a65-a11b-42ce-8a86-78c3e8012b60

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
  0 < gammaPoissonPosteriorMean a b e c := by
  unfold gammaPoissonPosteriorMean gammaPoissonPosteriorShape gammaPoissonPosteriorRate
  exact div_pos (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _))
    (add_pos_of_pos_of_nonneg hb he)
