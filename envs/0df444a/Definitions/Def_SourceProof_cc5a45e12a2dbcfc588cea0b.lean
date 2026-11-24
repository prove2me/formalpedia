-- Prove2me | Definitions.Def_SourceProof_cc5a45e12a2dbcfc588cea0b
-- name    : SourceProof_cc5a45e12a2dbcfc588cea0b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:07:46.978805+00:00
-- url     : https://prove2.me/theorems/ef45322f-fc67-439e-b57c-c0a4dea67cf3
-- title:
--   StochLean source theorem: StochLean.eVariationOn_neg

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

theorem _root_.Prove2MeSourceProof.h_cc5a45e12a2dbcfc588cea0b (f : α → E) (s : Set α) :
    eVariationOn (fun t ↦ -f t) s = eVariationOn f s := by
  simp only [eVariationOn, edist_neg_neg]
end StochLean


