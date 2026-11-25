-- Prove2me | Definitions.Def_SourceProof_5b07d4f9c2e48adbc1637f39
-- name    : SourceProof_5b07d4f9c2e48adbc1637f39
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:31:03.665653+00:00
-- url     : https://prove2.me/theorems/2464fd0a-b0cc-4d0c-84e0-f7fb5e62741b
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.exponent_zeroTriplet

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F011

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
theorem _root_.Prove2MeSourceProof.h_5b07d4f9c2e48adbc1637f39 (t : ℝ) : zero.exponent t = 0 := by
  simp [ProbabilityTheory.LevyTriplet.zero, ProbabilityTheory.LevyTriplet.exponent]
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


