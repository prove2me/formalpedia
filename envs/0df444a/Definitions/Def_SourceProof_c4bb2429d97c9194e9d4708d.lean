-- Prove2me | Definitions.Def_SourceProof_c4bb2429d97c9194e9d4708d
-- name    : SourceProof_c4bb2429d97c9194e9d4708d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:45:43.273533+00:00
-- url     : https://prove2.me/theorems/ee12a72e-099a-5c83-9d1e-eaf43fba25b3
-- title:
--   StochLean source theorem: StochLean.normSquarePairSum_terminal

import Definitions.Def_StochLean_Analysis_PathVariation_VectorPairSums_F000
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Endpoint-pair sums weighted by vector increment norms

The sums retain the partial terminal cell. Their energy is bounded by the
coordinate square sums; no vector stochastic quadratic variation is defined.
-/

@[expose] public section

open Set Finset
open scoped NNReal

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] {S : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_c4bb2429d97c9194e9d4708d (π : TimePartition S) (Φ : E → E → ℝ)
    (x : ℝ≥0 → E) : normSquarePairSum π Φ x S =
      ∑ i : Fin π.size, Φ (x (π.left i)) (x (π.right i)) *
        ‖x (π.right i) - x (π.left i)‖ ^ 2 := by
  apply sum_congr rfl
  intro i _
  rw [min_eq_left (show π.left i ≤ S from (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f π) i.castSucc),
    min_eq_left (show π.right i ≤ S from (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f π) i.succ)]
end StochLean


