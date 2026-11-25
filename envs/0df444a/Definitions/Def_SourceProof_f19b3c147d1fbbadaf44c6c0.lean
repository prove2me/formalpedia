-- Prove2me | Definitions.Def_SourceProof_f19b3c147d1fbbadaf44c6c0
-- name    : SourceProof_f19b3c147d1fbbadaf44c6c0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:31:11.938368+00:00
-- url     : https://prove2.me/theorems/4aa4a08e-7606-403d-927f-b969bc36662d
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.exponent_add

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F015
import Definitions.Def_SourceProof_f62a285e39f3cce92855751f

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
theorem _root_.Prove2MeSourceProof.h_f19b3c147d1fbbadaf44c6c0 (η ξ : LevyTriplet) (t : ℝ) :
    (η.add ξ).exponent t = η.exponent t + ξ.exponent t := by
  simp only [ProbabilityTheory.LevyTriplet.exponent, ProbabilityTheory.LevyTriplet.add, NNReal.coe_add]
  rw [integral_add_measure ((_root_.Prove2MeSourceProof.h_f62a285e39f3cce92855751f η) t) ((_root_.Prove2MeSourceProof.h_f62a285e39f3cce92855751f ξ) t)]
  push_cast
  ring
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


