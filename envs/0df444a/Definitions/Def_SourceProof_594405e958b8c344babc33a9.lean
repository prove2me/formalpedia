-- Prove2me | Definitions.Def_SourceProof_594405e958b8c344babc33a9
-- name    : SourceProof_594405e958b8c344babc33a9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:30:46.192801+00:00
-- url     : https://prove2.me/theorems/f15fb274-144f-4db6-96f9-22ede9e616c9
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.finiteRestriction_jumpMeasure_finite

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F022
import Definitions.Def_SourceProof_be003b4edbf4c065ede40d07

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

theorem _root_.Prove2MeSourceProof.h_594405e958b8c344babc33a9 (η : LevyTriplet) (n : ℕ) :
    IsFiniteMeasure (η.finiteRestriction n).jumpMeasure := by
  apply IsFiniteMeasure.mk
  rw [ProbabilityTheory.LevyTriplet.finiteRestriction, Measure.restrict_apply_univ]
  exact (_root_.Prove2MeSourceProof.h_be003b4edbf4c065ede40d07 η.isLevyMeasure_jumpMeasure) n
end LevyTriplet

end ProbabilityTheory


