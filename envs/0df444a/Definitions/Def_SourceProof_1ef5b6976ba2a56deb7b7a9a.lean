-- Prove2me | Definitions.Def_SourceProof_1ef5b6976ba2a56deb7b7a9a
-- name    : SourceProof_1ef5b6976ba2a56deb7b7a9a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:52.882671+00:00
-- url     : https://prove2.me/theorems/7af81ad6-461a-4792-bdd1-d8e17c002145
-- title:
--   StochLean source theorem: StochLean.negativeVariationStieltjes_measure_le

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_22908da40768e213d2860fb4
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite-horizon integration against a locally BV path

The increment integral on `(s,t]` is the difference of integrals against the
canonical positive and negative Stieltjes components. Integrability is measured
against their sum, the total-variation measure. The source integral from time
zero additionally contains `f 0 * x 0`; this is not a measure atom.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace StochLean

variable (x : ℝ≥0 → ℝ) (hx : LocallyBoundedVariationOn x univ)
  (hr : ∀ t, ContinuousWithinAt x (Ici t) t)

theorem _root_.Prove2MeSourceProof.h_1ef5b6976ba2a56deb7b7a9a :
    (negativeVariationStieltjes x hx hr).measure ≤ (totalVariationStieltjes x hx hr).measure := by
  rw [_root_.Prove2MeSourceProof.h_22908da40768e213d2860fb4]
  exact Measure.le_add_left le_rfl
variable {x hx hr} {f g : ℝ≥0 → ℝ} {s t : ℝ≥0}

end StochLean


