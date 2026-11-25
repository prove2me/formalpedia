-- Prove2me | Definitions.Def_SourceProof_757c0e14bc5574fd4d5f86ba
-- name    : SourceProof_757c0e14bc5574fd4d5f86ba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:36:52.957711+00:00
-- url     : https://prove2.me/theorems/fbdbc868-f7ce-5812-b432-8892ad95d564
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.triplet_represents_law

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F007
import Definitions.Def_SourceProof_26568eb87814e28c4992c1f4
import Definitions.Def_SourceProof_3dc6ba7e718cde1be7f01e13

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

theorem _root_.Prove2MeSourceProof.h_757c0e14bc5574fd4d5f86ba (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hzero : (μ : Measure ℝ) {0} = 0) :
    (triplet r μ hzero).Represents (law r μ) := by
  intro t
  rw [_root_.Prove2MeSourceProof.h_26568eb87814e28c4992c1f4, _root_.Prove2MeSourceProof.h_3dc6ba7e718cde1be7f01e13]
end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


