-- Prove2me | Definitions.Def_SourceProof_51202d8bd6fc2fc133a2c10d
-- name    : SourceProof_51202d8bd6fc2fc133a2c10d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:30:33.651881+00:00
-- url     : https://prove2.me/theorems/961625fb-bdfd-525e-8a93-f55dce8905b9
-- title:
--   StochLean source theorem: StochLean.quadraticVariationSum_eq_of_range_eq

import Definitions.Def_SourceProof_865fce00f7b48b46b8e94939

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Endpoint-set invariance of deterministic sums

An ordered list may repeat its endpoints. Nonempty cells, however, are determined uniquely by
the endpoint set. Thus sums of cell contributions that vanish on empty cells depend only on
the endpoint set, rather than its enumeration.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean.TimePartition

variable {T : ℝ≥0}

end StochLean.TimePartition

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_51202d8bd6fc2fc133a2c10d {T : ℝ≥0} {π ρ : TimePartition T}
    (heq : Set.range π.point = Set.range ρ.point) (f : ℝ≥0 → ℝ) :
    quadraticVariationSum π f = quadraticVariationSum ρ f :=
  _root_.Prove2MeSourceProof.h_865fce00f7b48b46b8e94939 heq (fun a b ↦ (f b - f a) ^ 2) (by simp)
end StochLean


