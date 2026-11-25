-- Prove2me | Definitions.Def_SourceProof_2669f41d4ab2eaa6e9935e14
-- name    : SourceProof_2669f41d4ab2eaa6e9935e14
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:29:54.101195+00:00
-- url     : https://prove2.me/theorems/13b129b7-7430-55e2-a3b6-d839acb010b8
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.continuous_exponent

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_SourceProof_71a9e7e789f4050f49460788

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

theorem _root_.Prove2MeSourceProof.h_2669f41d4ab2eaa6e9935e14 (η : LevyTriplet) : Continuous η.exponent := by
  have hjump := (_root_.Prove2MeSourceProof.h_71a9e7e789f4050f49460788 η)
  unfold ProbabilityTheory.LevyTriplet.exponent
  fun_prop
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


