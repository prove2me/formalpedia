-- Prove2me | Definitions.Def_SourceProof_1d577702c68f7f6df1204f28
-- name    : SourceProof_1d577702c68f7f6df1204f28
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:32.531585+00:00
-- url     : https://prove2.me/theorems/7be1a572-562d-473b-bad3-254eb89fa431
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.measurableSet_levyIdentificationSet

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F010

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

theorem _root_.Prove2MeSourceProof.h_1d577702c68f7f6df1204f28 (n : ℕ) :
    MeasurableSet (levyIdentificationSet n) := by
  unfold ProbabilityTheory.LevyTriplet.levyIdentificationSet
  measurability
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


