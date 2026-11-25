-- Prove2me | Definitions.Def_SourceProof_0a41c493088d6b6495e37e42
-- name    : SourceProof_0a41c493088d6b6495e37e42
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:30:44.286201+00:00
-- url     : https://prove2.me/theorems/f5630f9d-ca19-56fb-9bf8-ec338339b53d
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStronglyOptional_of_cadlag

import Definitions.Def_StochLean_Probability_Process_Measurability_Optional_F001
import Definitions.Def_SourceProof_a668d32c17f2633459e41237

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

end Filtration

variable {E : Type*} [TopologicalSpace E] {F : Filtration ℝ≥0 mΩ}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_0a41c493088d6b6495e37e42 {X : ℝ≥0 → Ω → ℝ} (ha : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (fun t ↦ X t ω)) : IsStronglyOptional F X :=
  ((_root_.Prove2MeSourceProof.h_a668d32c17f2633459e41237 ha) hc).stronglyMeasurable
end Adapted

end MeasureTheory


