-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F021
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F021
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:20:58.804179+00:00
-- url     : https://prove2.me/theorems/03150597-846f-59a3-9cde-c6b0123a672d
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F021

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F013

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

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

/-- The probability law represented by a triplet with finite jump measure: deterministic drift,
Gaussian part, and the zero-safe finite-intensity compound-Poisson part. -/
noncomputable def finiteJumpLaw (η : LevyTriplet) [IsFiniteMeasure η.jumpMeasure] :
    ProbabilityMeasure ℝ :=
  let νf : FiniteMeasure ℝ := ⟨η.jumpMeasure, inferInstance⟩
  ProbabilityMeasure.conv
    (ProbabilityMeasure.conv
      (ProbabilityMeasure.pointMass
        (η.drift - ∫ x, levyTruncation x ∂η.jumpMeasure))
      (gaussianLaw 0 η.gaussianVariance))
    (CompoundPoisson.ofFiniteMeasure νf)
end LevyTriplet

end ProbabilityTheory


