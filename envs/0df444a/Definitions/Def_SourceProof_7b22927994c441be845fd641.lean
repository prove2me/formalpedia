-- Prove2me | Definitions.Def_SourceProof_7b22927994c441be845fd641
-- name    : SourceProof_7b22927994c441be845fd641
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:50.229873+00:00
-- url     : https://prove2.me/theorems/963e86e4-ab2f-4ba1-8fa8-3d0f50638459
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.nnrealSMul_one

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
theorem _root_.Prove2MeSourceProof.h_7b22927994c441be845fd641 (η : LevyTriplet) : η.nnrealSMul 1 = η := by
  cases η
  simp [ProbabilityTheory.LevyTriplet.nnrealSMul]
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


