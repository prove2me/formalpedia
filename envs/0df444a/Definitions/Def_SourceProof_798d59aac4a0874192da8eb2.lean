-- Prove2me | Definitions.Def_SourceProof_798d59aac4a0874192da8eb2
-- name    : SourceProof_798d59aac4a0874192da8eb2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:27.688803+00:00
-- url     : https://prove2.me/theorems/36d539b4-df92-4109-80f2-7e3c5ff896a4
-- title:
--   StochLean source theorem: StochLean.locallyBoundedVariationOn_sub

import Definitions.Def_SourceProof_1d493e8fd45664a706227178

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

theorem _root_.Prove2MeSourceProof.h_798d59aac4a0874192da8eb2 {f g : α → E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (fun t ↦ f t - g t) s :=
  fun a b ha hb ↦ _root_.Prove2MeSourceProof.h_1d493e8fd45664a706227178 (hf a b ha hb) (hg a b ha hb)
end StochLean


