-- Prove2me | Definitions.Def_SourceProof_100a4fbbee9cf0e8517b3b4d
-- name    : SourceProof_100a4fbbee9cf0e8517b3b4d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:16.350689+00:00
-- url     : https://prove2.me/theorems/621ca4d3-3246-48fb-9c67-ef5cd2cf7116
-- title:
--   StochLean source theorem: StochLean.TimePartition.endpoint_le_left_or_right_le

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Reflection of deterministic paths and invariance of square sums

There is no probability space in this layer. Flipping all increments of one interval preserves
every square sum whose partition contains both endpoints, including repeated endpoints.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean

namespace TimePartition

theorem _root_.Prove2MeSourceProof.h_100a4fbbee9cf0e8517b3b4d {T : ℝ≥0} (π : TimePartition T)
    {a : ℝ≥0} (ha : a ∈ Set.range π.point) (i : Fin π.size) :
    a ≤ π.left i ∨ π.right i ≤ a := by
  obtain ⟨j, rfl⟩ := ha
  by_cases hj : j ≤ i.castSucc
  · exact Or.inl (π.monotone_point hj)
  · right
    apply π.monotone_point
    change i.val + 1 ≤ j.val
    exact Nat.succ_le_of_lt (lt_of_not_ge hj)
end TimePartition

end StochLean


