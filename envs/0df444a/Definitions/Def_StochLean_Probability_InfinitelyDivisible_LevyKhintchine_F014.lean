-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F014
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F014
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:26:45.438075+00:00
-- url     : https://prove2.me/theorems/aada750a-1177-42d1-b8ce-1fdb20153069
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F014

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

/-- The no-jump Gaussian triplet. -/
noncomputable def gaussian (m : ℝ) (v : ℝ≥0) : LevyTriplet where
  gaussianVariance := v
  drift := m
  jumpMeasure := 0
  isLevyMeasure_jumpMeasure := by simp [IsLevyMeasure]
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


