-- Prove2me | Definitions.Def_SourceProof_1c883159017bdf91b31257ab
-- name    : SourceProof_1c883159017bdf91b31257ab
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:57.858121+00:00
-- url     : https://prove2.me/theorems/bae91188-f0d3-4e45-accb-770b965c72a2
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.measurable_secondDifferenceWeight

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F008
import Definitions.Def_SourceProof_f9b33963924eb7ac5401881f

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

theorem _root_.Prove2MeSourceProof.h_1c883159017bdf91b31257ab (s : ℝ) : Measurable (secondDifferenceWeight s) := by
  unfold ProbabilityTheory.LevyTriplet.secondDifferenceWeight
  exact (_root_.Prove2MeSourceProof.h_f9b33963924eb7ac5401881f s).add
    (_root_.Prove2MeSourceProof.h_f9b33963924eb7ac5401881f (-s)) |>.nnnorm
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


