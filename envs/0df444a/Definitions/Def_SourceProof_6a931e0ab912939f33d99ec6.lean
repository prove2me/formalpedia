-- Prove2me | Definitions.Def_SourceProof_6a931e0ab912939f33d99ec6
-- name    : SourceProof_6a931e0ab912939f33d99ec6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:17:50.6872+00:00
-- url     : https://prove2.me/theorems/b077c7d1-d3d8-4f1a-89e4-28b4dae34995
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.positiveVariationProcess_of_rightContinuous

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Jordan_F000
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_SourceProof_e6425243a41057923256952a

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Canonical increasing components of a finite-variation process

Both components start at zero. They decompose increments, with the initial
random variable kept separate. No integrability of the variation is assumed.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_6a931e0ab912939f33d99ec6 (ha : Adapted F X)
    (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω)) :
    Adapted F (ProbabilityTheory.positiveVariationProcess X) := by
  intro t
  have h := (_root_.Prove2MeSourceProof.h_e6425243a41057923256952a ha) hr t
  exact ((h.add (ha t)).sub ((ha 0).mono (F.mono bot_le) le_rfl)).div_const 2
end Adapted

end MeasureTheory


