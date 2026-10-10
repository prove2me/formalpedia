-- Prove2me | solution 1 for ActuarialValuation.negBinCountVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:02:27.702049+00:00
-- url     : https://prove2.me/submissions/7fd64a7b-36cf-4461-b40e-c8362f61288f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountVariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : ℕ) (p : ℝ)
  (hp0 : 0 ≤ p) (hp1 : p < 1) :
  0 ≤ negBinCountVariance r p := by
  have hden : 0 < 1 - p := by linarith
  unfold negBinCountVariance
  positivity
