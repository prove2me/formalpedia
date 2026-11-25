-- Prove2me | Definitions.Def_SourceProof_f62a285e39f3cce92855751f
-- name    : SourceProof_f62a285e39f3cce92855751f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:22:02.02587+00:00
-- url     : https://prove2.me/theorems/1de54396-6d92-4c8c-af6d-79178ec07aca
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.integrable_exponent_jump

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005
import Definitions.Def_SourceProof_c3b700cf3e07c09b0f6a6eee

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

theorem _root_.Prove2MeSourceProof.h_f62a285e39f3cce92855751f (η : LevyTriplet) (t : ℝ) :
    Integrable (levyExponentIntegrand t) η.jumpMeasure :=
  (_root_.Prove2MeSourceProof.h_c3b700cf3e07c09b0f6a6eee η.isLevyMeasure_jumpMeasure) t
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


