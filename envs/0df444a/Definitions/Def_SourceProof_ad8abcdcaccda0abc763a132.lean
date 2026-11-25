-- Prove2me | Definitions.Def_SourceProof_ad8abcdcaccda0abc763a132
-- name    : SourceProof_ad8abcdcaccda0abc763a132
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:18.766587+00:00
-- url     : https://prove2.me/theorems/0406a7d7-bd16-5845-80e3-3bfae87b7912
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.nnrealSMul_add

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F015
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F016

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

theorem _root_.Prove2MeSourceProof.h_ad8abcdcaccda0abc763a132 (r s : ℝ≥0) (η : LevyTriplet) :
    η.nnrealSMul (r + s) = (η.nnrealSMul r).add (η.nnrealSMul s) := by
  cases η
  simp [ProbabilityTheory.LevyTriplet.nnrealSMul, ProbabilityTheory.LevyTriplet.add, add_smul, add_mul]
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


