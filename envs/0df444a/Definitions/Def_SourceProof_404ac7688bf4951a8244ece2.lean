-- Prove2me | Definitions.Def_SourceProof_404ac7688bf4951a8244ece2
-- name    : SourceProof_404ac7688bf4951a8244ece2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:25:32.846152+00:00
-- url     : https://prove2.me/theorems/7d8816ba-0824-42f5-b408-dc51f164adbe
-- title:
--   StochLean source theorem: ProbabilityTheory.strictLeftGrid_zero

import Definitions.Def_StochLean_Probability_Process_Measurability_PredictableGrid_F000

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

@[simp] theorem _root_.Prove2MeSourceProof.h_404ac7688bf4951a8244ece2 (δ : ℝ≥0) : strictLeftGrid δ 0 = 0 := by
  simp [ProbabilityTheory.strictLeftGrid]
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


