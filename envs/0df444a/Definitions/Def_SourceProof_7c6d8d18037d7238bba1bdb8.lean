-- Prove2me | Definitions.Def_SourceProof_7c6d8d18037d7238bba1bdb8
-- name    : SourceProof_7c6d8d18037d7238bba1bdb8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:22.899542+00:00
-- url     : https://prove2.me/theorems/30a1b532-3a6e-4d96-b182-a26e5433d9f6
-- title:
--   StochLean source theorem: StochLean.quadraticPairSum_terminal

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F004
import Definitions.Def_StochLean_Analysis_PathVariation_QuadraticPairSums_F000
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Quadratic-pair estimates after removing finitely selected cells -/

@[expose] public section

open Set Finset
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_7c6d8d18037d7238bba1bdb8 {T : ℝ≥0} (π : TimePartition T)
    (Φ : ℝ → ℝ → ℝ) (x : ℝ≥0 → ℝ) :
    quadraticPairSum π Φ x T =
      ∑ i : Fin π.size, Φ (x (π.left i)) (x (π.right i)) * (π.increment x i) ^ 2 := by
  apply sum_congr rfl
  intro i _
  rw [min_eq_left (show π.left i ≤ T from (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f π) i.castSucc),
    min_eq_left (show π.right i ≤ T from (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f π) i.succ)]
  rfl
end StochLean


