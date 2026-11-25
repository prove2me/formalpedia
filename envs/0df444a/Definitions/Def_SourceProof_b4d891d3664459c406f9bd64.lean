-- Prove2me | Definitions.Def_SourceProof_b4d891d3664459c406f9bd64
-- name    : SourceProof_b4d891d3664459c406f9bd64
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:54.14731+00:00
-- url     : https://prove2.me/theorems/07c883af-fb2d-4ba1-9dbb-6466bca5fd02
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.secondDifference_exponent_eq

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006

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

theorem _root_.Prove2MeSourceProof.h_b4d891d3664459c406f9bd64 (η : LevyTriplet) (s t : ℝ) :
    η.exponent (t + s) + η.exponent (t - s) - 2 * η.exponent t =
      -(((η.gaussianVariance : ℝ) * s ^ 2 : ℝ) : ℂ) +
        ((∫ x, levyExponentIntegrand (t + s) x ∂η.jumpMeasure) +
        (∫ x, levyExponentIntegrand (t - s) x ∂η.jumpMeasure) -
        2 * ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure) := by
  simp only [ProbabilityTheory.LevyTriplet.exponent]
  push_cast
  ring
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


