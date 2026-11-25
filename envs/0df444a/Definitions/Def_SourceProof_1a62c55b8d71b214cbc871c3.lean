-- Prove2me | Definitions.Def_SourceProof_1a62c55b8d71b214cbc871c3
-- name    : SourceProof_1a62c55b8d71b214cbc871c3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:51:30.781202+00:00
-- url     : https://prove2.me/theorems/7415603f-d2e2-41c7-942b-c8d91fc11d91
-- title:
--   StochLean source theorem: MeasureTheory.IsStronglyOptional.stronglyAdapted

import Definitions.Def_SourceProof_96b55b0bbab7c4daf4fac947

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
theorem _root_.Prove2MeSourceProof.h_1a62c55b8d71b214cbc871c3 {X : ℝ≥0 → Ω → E}
    (hX : IsStronglyOptional F X) : StronglyAdapted F X :=
  (_root_.Prove2MeSourceProof.h_96b55b0bbab7c4daf4fac947 hX).stronglyAdapted
end IsStronglyOptional

end MeasureTheory


