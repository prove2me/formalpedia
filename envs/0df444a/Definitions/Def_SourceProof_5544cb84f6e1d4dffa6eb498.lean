-- Prove2me | Definitions.Def_SourceProof_5544cb84f6e1d4dffa6eb498
-- name    : SourceProof_5544cb84f6e1d4dffa6eb498
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:30:42.064316+00:00
-- url     : https://prove2.me/theorems/44afc9cc-34c6-57ce-8a5f-e4d81c93478d
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStronglyPredictable_leftLimitProcess_of_cadlag

import Definitions.Def_StochLean_Probability_Process_Measurability_PredictableGrid_F000
import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_354b37228f98fe5fdec5bcbb
import Definitions.Def_SourceProof_6fe8e798f5fa5227db6c7521
import Definitions.Def_SourceProof_f006d78a6e9979cf18230f20

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Predictability from left-continuous adapted paths

Mathlib's predictable sigma-field remains the canonical owner. Strict-past grids
prove the source Chapter III bridge. For merely almost-sure path regularity a
single exceptional event is removed: the conclusion is an indistinguishable
predictable version, not predictability of arbitrary exceptional trajectories.
This file does not extend the Chapter II integral to all predictable integrands.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_5544cb84f6e1d4dffa6eb498 (ha : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (fun t ↦ X t ω)) :
    IsStronglyPredictable F (leftLimitProcess X) :=
  (_root_.Prove2MeSourceProof.h_354b37228f98fe5fdec5bcbb ((_root_.Prove2MeSourceProof.h_6fe8e798f5fa5227db6c7521 ha) hc))
    (fun ω ↦ (_root_.Prove2MeSourceProof.h_f006d78a6e9979cf18230f20 (hc ω)).1)
end Adapted

end MeasureTheory


