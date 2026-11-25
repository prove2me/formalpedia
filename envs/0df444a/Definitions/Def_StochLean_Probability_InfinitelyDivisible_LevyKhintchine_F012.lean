-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F012
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F012
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:10.341978+00:00
-- url     : https://prove2.me/theorems/cd0ee10a-1c54-5212-9b8a-7c14720c725b
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F012

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace LevyTriplet

/-- The canonical triplet of a Dirac law under the fixed truncation. -/
noncomputable def pointMass (x : ℝ) : LevyTriplet where
  gaussianVariance := 0
  drift := x
  jumpMeasure := 0
  isLevyMeasure_jumpMeasure := by simp [IsLevyMeasure]
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


