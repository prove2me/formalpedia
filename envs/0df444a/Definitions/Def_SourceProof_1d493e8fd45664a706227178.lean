-- Prove2me | Definitions.Def_SourceProof_1d493e8fd45664a706227178
-- name    : SourceProof_1d493e8fd45664a706227178
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:02.67415+00:00
-- url     : https://prove2.me/theorems/27e58481-e519-4339-aec2-44e667b46426
-- title:
--   StochLean source theorem: StochLean.boundedVariationOn_sub

import Definitions.Def_SourceProof_67669bc4ed9cd6e8810cbe85
import Definitions.Def_SourceProof_cc5a45e12a2dbcfc588cea0b

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

theorem _root_.Prove2MeSourceProof.h_1d493e8fd45664a706227178 {f g : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun t ↦ f t - g t) s := by
  have hn : BoundedVariationOn (fun t ↦ -g t) s := by
    change eVariationOn (fun t ↦ -g t) s ≠ ∞
    rwa [_root_.Prove2MeSourceProof.h_cc5a45e12a2dbcfc588cea0b]
  simpa only [sub_eq_add_neg] using _root_.Prove2MeSourceProof.h_67669bc4ed9cd6e8810cbe85 hf hn
end StochLean


