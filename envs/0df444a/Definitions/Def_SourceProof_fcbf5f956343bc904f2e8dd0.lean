-- Prove2me | Definitions.Def_SourceProof_fcbf5f956343bc904f2e8dd0
-- name    : SourceProof_fcbf5f956343bc904f2e8dd0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:02:37.787491+00:00
-- url     : https://prove2.me/theorems/c9089658-928b-4365-96a2-38585ea75dd1
-- title:
--   StochLean source theorem: ProbabilityTheory.strictLeftGrid_le

import Definitions.Def_StochLean_Probability_Process_Measurability_PredictableGrid_F000
import Definitions.Def_SourceProof_404ac7688bf4951a8244ece2
import Definitions.Def_SourceProof_7a587c2d7b097459d1fe61a8

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Strict-past deterministic grids for predictable processes

At a positive grid endpoint the preceding cell is used, as required for predictable
`(s,t]` rectangles. At zero the original initial value is retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_fcbf5f956343bc904f2e8dd0 {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ≥0) : strictLeftGrid δ t ≤ t := by
  rcases eq_or_lt_of_le (show 0 ≤ t from bot_le) with ht | ht
  · subst t
    rw [_root_.Prove2MeSourceProof.h_404ac7688bf4951a8244ece2]
  · exact (_root_.Prove2MeSourceProof.h_7a587c2d7b097459d1fe61a8 hδ ht).1.le
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


