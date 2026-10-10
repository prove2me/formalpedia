-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonPosteriorRate_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:40:22.280123+00:00
-- url     : https://prove2.me/submissions/c3fb8d0a-078f-47a3-8e26-a30051d23615

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b e : ℝ)
  (hb : 0 < b) (he : 0 ≤ e) :
  0 < gammaPoissonPosteriorRate b e := by
  change 0 < b + e
  exact add_pos_of_pos_of_nonneg hb he
