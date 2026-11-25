-- Prove2me | Definitions.Def_SourceProof_6781543f132c74b0c839e817
-- name    : SourceProof_6781543f132c74b0c839e817
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:54:41.671223+00:00
-- url     : https://prove2.me/theorems/f943230b-13f4-539c-9765-81b80ff976fc
-- title:
--   StochLean source theorem: MeasureTheory.IsStronglyPredictable.isStronglyOptional

import Definitions.Def_StochLean_Probability_Process_Measurability_Optional_F001
import Definitions.Def_SourceProof_238a30ea26f38f7600aab333

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

namespace IsStronglyPredictable
theorem _root_.Prove2MeSourceProof.h_6781543f132c74b0c839e817 {X : ℝ≥0 → Ω → E}
    (hX : IsStronglyPredictable F X) : IsStronglyOptional F X :=
  hX.mono (_root_.Prove2MeSourceProof.h_238a30ea26f38f7600aab333 F)
end IsStronglyPredictable

end MeasureTheory


