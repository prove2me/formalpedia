-- Prove2me | Definitions.Def_SourceProof_82c6a8d7f62bdd2579a434fc
-- name    : SourceProof_82c6a8d7f62bdd2579a434fc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:36:51.042429+00:00
-- url     : https://prove2.me/theorems/088c84a7-5e8b-45be-9e60-be882ad4ec96
-- title:
--   StochLean source theorem: MeasureTheory.Filtration.optional_le_progressive

import Definitions.Def_StochLean_Probability_Process_Measurability_Optional_F000
import Definitions.Def_SourceProof_6a141fa6412d14db4fc15aeb
import Definitions.Def_SourceProof_84e43ea7d3e275425e367f8b

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The optional sigma-field and the source inclusion chain

Protter III.1 defines the optional sigma-field using adapted cadlag real
processes. Everywhere path regularity is used in its generators. For merely
almost-sure cadlag paths the bridge constructs an indistinguishable optional
version; it does not assert optionality of arbitrary exceptional trajectories.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace Filtration

end Filtration

namespace Filtration

theorem _root_.Prove2MeSourceProof.h_82c6a8d7f62bdd2579a434fc (F : Filtration ℝ≥0 mΩ) : F.optional ≤ F.progressive := by
  refine iSup_le fun X ↦ iSup_le fun ha ↦ iSup_le fun hc ↦ ?_
  have hsa : StronglyAdapted F X := fun t ↦ (ha t).stronglyMeasurable
  have hp := ((_root_.Prove2MeSourceProof.h_6a141fa6412d14db4fc15aeb hsa) (fun ω ↦ (hc ω).1)).isProgressive
  exact (((_root_.Prove2MeSourceProof.h_84e43ea7d3e275425e367f8b F)).mpr hp).comap_le
end Filtration

variable {E : Type*} [TopologicalSpace E] {F : Filtration ℝ≥0 mΩ}

end MeasureTheory


