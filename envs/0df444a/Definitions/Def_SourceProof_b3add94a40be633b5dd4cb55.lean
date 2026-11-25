-- Prove2me | Definitions.Def_SourceProof_b3add94a40be633b5dd4cb55
-- name    : SourceProof_b3add94a40be633b5dd4cb55
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:23:05.808124+00:00
-- url     : https://prove2.me/theorems/d8704a8b-e44e-4911-a445-d5e30c6c6a7a
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.restrict_iUnion_spanningLevel

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005
import Definitions.Def_SourceProof_6e49c08e4f02ca77a891cfb5
import Definitions.Def_SourceProof_86ff457032bada5981439e9c
import Definitions.Def_SourceProof_e46e0dc5c645a65952f0c22f

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

theorem _root_.Prove2MeSourceProof.h_b3add94a40be633b5dd4cb55 (η : LevyTriplet) :
    η.jumpMeasure.restrict (⋃ n, IsLevyMeasure.spanningLevel n) = η.jumpMeasure := by
  rw [_root_.Prove2MeSourceProof.h_e46e0dc5c645a65952f0c22f]
  have hsplit := η.jumpMeasure.restrict_compl_add_restrict
    (MeasurableSet.singleton (0 : ℝ))
  rw [Measure.restrict_singleton, (_root_.Prove2MeSourceProof.h_6e49c08e4f02ca77a891cfb5 η.isLevyMeasure_jumpMeasure)] at hsplit
  simpa using hsplit
end LevyTriplet

end ProbabilityTheory


