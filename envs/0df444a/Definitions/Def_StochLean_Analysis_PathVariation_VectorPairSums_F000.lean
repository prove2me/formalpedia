-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_VectorPairSums_F000
-- name    : StochLean_Analysis_PathVariation_VectorPairSums_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:29.262357+00:00
-- url     : https://prove2.me/theorems/eaa86372-a10d-472e-af5f-f578f88254ca
-- title:
--   StochLean: Analysis.PathVariation.VectorPairSums F000

import Definitions.Def_StochLean_Analysis_PathVariation_VectorEnergy_F000

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

noncomputable def normSquarePairSum (π : TimePartition S)
    (Φ : E → E → ℝ) (x : ℝ≥0 → E) (t : ℝ≥0) : ℝ :=
  ∑ i : Fin π.size,
    Φ (x (min (π.left i) t)) (x (min (π.right i) t)) *
      ‖x (min (π.right i) t) - x (min (π.left i) t)‖ ^ 2
end StochLean


