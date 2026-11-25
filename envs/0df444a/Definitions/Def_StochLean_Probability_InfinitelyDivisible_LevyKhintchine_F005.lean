-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:11:08.798672+00:00
-- url     : https://prove2.me/theorems/3ee91b8d-8127-4613-b89a-986771baf2f7
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F005

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F000
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F004

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

/-- A real Lévy triplet under the fixed strict truncation convention. -/
structure LevyTriplet where
  gaussianVariance : ℝ≥0
  drift : ℝ
  jumpMeasure : Measure ℝ
  isLevyMeasure_jumpMeasure : IsLevyMeasure jumpMeasure
namespace LevyTriplet

/-- Drift expressed under an admissible alternative truncation.  The sign is fixed by requiring
the resulting exponent to be identical to the strict-truncation exponent. -/
noncomputable def driftUnderTruncation (η : LevyTriplet) (k : ℝ → ℝ) : ℝ :=
  η.drift + ∫ x, (k x - levyTruncation x) ∂η.jumpMeasure
/-- Levy exponent displayed with an explicit truncation and its corresponding drift. -/
noncomputable def exponentWithTruncation (η : LevyTriplet) (k : ℝ → ℝ) (t : ℝ) : ℂ :=
  -((((η.gaussianVariance : ℝ) / 2) * t ^ 2 : ℝ) : ℂ) +
    (((η.driftUnderTruncation k * t : ℝ) : ℂ) * Complex.I) +
      ∫ x, levyExponentIntegrandWithTruncation k t x ∂η.jumpMeasure
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


