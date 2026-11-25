-- Prove2me | Definitions.Def_SourceProof_e9384a57ef8c9b4459272f2a
-- name    : SourceProof_e9384a57ef8c9b4459272f2a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:43.254341+00:00
-- url     : https://prove2.me/theorems/1874c1f4-f7f0-5118-ab34-e70f91aa508a
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.weightedJumpMeasure_singleton_zero

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F009
import Definitions.Def_SourceProof_6e49c08e4f02ca77a891cfb5

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

theorem _root_.Prove2MeSourceProof.h_e9384a57ef8c9b4459272f2a (η : LevyTriplet) (s : ℝ) :
    weightedJumpMeasure η s {0} = 0 := by
  exact withDensity_absolutelyContinuous η.jumpMeasure _
    (_root_.Prove2MeSourceProof.h_6e49c08e4f02ca77a891cfb5 η.isLevyMeasure_jumpMeasure)
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


