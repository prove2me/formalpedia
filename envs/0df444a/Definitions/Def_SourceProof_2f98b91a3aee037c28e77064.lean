-- Prove2me | Definitions.Def_SourceProof_2f98b91a3aee037c28e77064
-- name    : SourceProof_2f98b91a3aee037c28e77064
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:10:49.969427+00:00
-- url     : https://prove2.me/theorems/77631716-1b28-46e0-8e12-2a2243c6da79
-- title:
--   StochLean source theorem: ProbabilityTheory.le_strictLeftGrid_add

import Definitions.Def_StochLean_Probability_Process_Measurability_PredictableGrid_F000
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

theorem _root_.Prove2MeSourceProof.h_2f98b91a3aee037c28e77064 {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ≥0) :
    t ≤ strictLeftGrid δ t + δ := by
  rcases eq_or_lt_of_le (show 0 ≤ t from bot_le) with ht | ht
  · subst t
    exact bot_le
  · exact (_root_.Prove2MeSourceProof.h_7a587c2d7b097459d1fe61a8 hδ ht).2
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


