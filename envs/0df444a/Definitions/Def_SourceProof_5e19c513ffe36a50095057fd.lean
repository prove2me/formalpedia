-- Prove2me | Definitions.Def_SourceProof_5e19c513ffe36a50095057fd
-- name    : SourceProof_5e19c513ffe36a50095057fd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:31:52.921743+00:00
-- url     : https://prove2.me/theorems/8da733b1-0d49-4e7f-a073-a793c2cf2fec
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.nnrealSMul_zero

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F011
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

@[simp]
theorem _root_.Prove2MeSourceProof.h_5e19c513ffe36a50095057fd (η : LevyTriplet) : η.nnrealSMul 0 = zero := by
  cases η
  simp [ProbabilityTheory.LevyTriplet.nnrealSMul, ProbabilityTheory.LevyTriplet.zero]
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


