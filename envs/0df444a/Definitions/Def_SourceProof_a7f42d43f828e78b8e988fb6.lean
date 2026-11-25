-- Prove2me | Definitions.Def_SourceProof_a7f42d43f828e78b8e988fb6
-- name    : SourceProof_a7f42d43f828e78b8e988fb6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:31:41.572019+00:00
-- url     : https://prove2.me/theorems/4719667a-5b47-4b36-81e7-91cbef7b492d
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.tripletOfFiniteMeasure_eq_zero

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F011
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F020

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

theorem _root_.Prove2MeSourceProof.h_a7f42d43f828e78b8e988fb6 (hzero : ((0 : FiniteMeasure ℝ) : Measure ℝ) {0} = 0) :
    tripletOfFiniteMeasure 0 hzero = LevyTriplet.zero := by
  rw [LevyTriplet.mk.injEq]
  simp [ProbabilityTheory.CompoundPoisson.tripletOfFiniteMeasure, ProbabilityTheory.LevyTriplet.zero]
end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


