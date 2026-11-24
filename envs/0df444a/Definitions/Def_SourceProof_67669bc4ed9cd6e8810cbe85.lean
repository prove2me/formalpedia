-- Prove2me | Definitions.Def_SourceProof_67669bc4ed9cd6e8810cbe85
-- name    : SourceProof_67669bc4ed9cd6e8810cbe85
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:24.296842+00:00
-- url     : https://prove2.me/theorems/76bd7be3-e1f4-41ca-9689-9f911357daef
-- title:
--   StochLean source theorem: StochLean.boundedVariationOn_add

import Definitions.Def_SourceProof_1577bffaa471a5ad54135ddc
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Arithmetic for the canonical bounded-variation predicate -/

@[expose] public section

open Set
open scoped ENNReal

namespace StochLean

variable {α E : Type*} [LinearOrder α] [NormedAddCommGroup E]

theorem _root_.Prove2MeSourceProof.h_67669bc4ed9cd6e8810cbe85 {f g : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun t ↦ f t + g t) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (_root_.Prove2MeSourceProof.h_1577bffaa471a5ad54135ddc f g s)
end StochLean


