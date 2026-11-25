-- Prove2me | Definitions.Def_SourceProof_b9df4492b15ca36c63738ab2
-- name    : SourceProof_b9df4492b15ca36c63738ab2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:34.719139+00:00
-- url     : https://prove2.me/theorems/dc45838a-b879-4ce3-b7ee-f8f9e2888598
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.exponent_pointMass

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F012

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

@[simp]
theorem _root_.Prove2MeSourceProof.h_b9df4492b15ca36c63738ab2 (x t : ℝ) : (pointMass x).exponent t =
    ((x * t : ℝ) : ℂ) * Complex.I := by
  simp [ProbabilityTheory.LevyTriplet.pointMass, ProbabilityTheory.LevyTriplet.exponent]
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


