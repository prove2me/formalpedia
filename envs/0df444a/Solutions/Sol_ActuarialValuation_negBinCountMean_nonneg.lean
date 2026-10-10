-- Prove2me | solution 1 for ActuarialValuation.negBinCountMean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:01:35.638636+00:00
-- url     : https://prove2.me/submissions/4f5a7e52-a716-4f18-8c2b-a790ca98a15e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : ℕ) (p : ℝ)
  (hp0 : 0 ≤ p) (hp1 : p < 1) :
  0 ≤ negBinCountMean r p := by
  have hden : 0 < 1 - p := by linarith
  unfold negBinCountMean
  positivity
