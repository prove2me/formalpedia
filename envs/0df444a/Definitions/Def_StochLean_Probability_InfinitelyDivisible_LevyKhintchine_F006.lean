-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:38.737809+00:00
-- url     : https://prove2.me/theorems/1967188c-740a-497f-9301-bacf7b341d87
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F006

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F001
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

/-- The real Lévy--Khintchine exponent under the fixed strict truncation convention. -/
noncomputable def exponent (η : LevyTriplet) (t : ℝ) : ℂ :=
  -((((η.gaussianVariance : ℝ) / 2) * t ^ 2 : ℝ) : ℂ) +
    ((η.drift * t : ℝ) : ℂ) * Complex.I +
      ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


