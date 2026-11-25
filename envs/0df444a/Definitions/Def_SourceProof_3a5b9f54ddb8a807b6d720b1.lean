-- Prove2me | Definitions.Def_SourceProof_3a5b9f54ddb8a807b6d720b1
-- name    : SourceProof_3a5b9f54ddb8a807b6d720b1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:31:07.264943+00:00
-- url     : https://prove2.me/theorems/fe366c52-eed6-4b19-b774-01f96855ae27
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.integrable_secondDifferenceWeight

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F008
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

theorem _root_.Prove2MeSourceProof.h_3a5b9f54ddb8a807b6d720b1 (η : LevyTriplet) (s : ℝ) :
    Integrable (fun x => (secondDifferenceWeight s x : ℝ)) η.jumpMeasure := by
  have h := ((_root_.Prove2MeSourceProof.h_f62a285e39f3cce92855751f η) s).add ((_root_.Prove2MeSourceProof.h_f62a285e39f3cce92855751f η) (-s))
  exact h.norm
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


