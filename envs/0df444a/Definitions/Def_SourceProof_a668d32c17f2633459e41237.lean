-- Prove2me | Definitions.Def_SourceProof_a668d32c17f2633459e41237
-- name    : SourceProof_a668d32c17f2633459e41237
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:20:21.906259+00:00
-- url     : https://prove2.me/theorems/c6c677bd-5f43-4630-bb92-5156a3dcfc16
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.measurable_optional_of_cadlag

import Definitions.Def_StochLean_Probability_Process_Measurability_Optional_F000

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

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_a668d32c17f2633459e41237 {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (ha : Adapted F X) (hc : ∀ ω, IsCadlagPath (fun t ↦ X t ω)) :
    Measurable[F.optional] (Function.uncurry X) :=
  measurable_iff_comap_le.mpr
    (le_iSup_of_le X (le_iSup_of_le ha (le_iSup_of_le hc le_rfl)))
end Adapted

namespace Filtration

end Filtration

variable {E : Type*} [TopologicalSpace E] {F : Filtration ℝ≥0 mΩ}

end MeasureTheory


