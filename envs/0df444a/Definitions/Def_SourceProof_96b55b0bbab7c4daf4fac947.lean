-- Prove2me | Definitions.Def_SourceProof_96b55b0bbab7c4daf4fac947
-- name    : SourceProof_96b55b0bbab7c4daf4fac947
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:44:59.633845+00:00
-- url     : https://prove2.me/theorems/d335d37a-da07-50de-aac6-44af9b3c768b
-- title:
--   StochLean source theorem: MeasureTheory.IsStronglyOptional.isStronglyProgressive

import Definitions.Def_StochLean_Probability_Process_Measurability_Optional_F001
import Definitions.Def_SourceProof_52c59e84cb8685e05e5d2278
import Definitions.Def_SourceProof_82c6a8d7f62bdd2579a434fc

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

namespace IsStronglyOptional
theorem _root_.Prove2MeSourceProof.h_96b55b0bbab7c4daf4fac947 {X : ℝ≥0 → Ω → E}
    (hX : IsStronglyOptional F X) : IsStronglyProgressive F X := by
  intro t
  exact (hX.mono (_root_.Prove2MeSourceProof.h_82c6a8d7f62bdd2579a434fc F)).comp_measurable ((_root_.Prove2MeSourceProof.h_52c59e84cb8685e05e5d2278 F) t)
end IsStronglyOptional

end MeasureTheory


