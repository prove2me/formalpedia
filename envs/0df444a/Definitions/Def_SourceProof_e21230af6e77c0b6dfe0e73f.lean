-- Prove2me | Definitions.Def_SourceProof_e21230af6e77c0b6dfe0e73f
-- name    : SourceProof_e21230af6e77c0b6dfe0e73f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:45.020066+00:00
-- url     : https://prove2.me/theorems/40865b9c-efb2-472a-89f9-9a972effd594
-- title:
--   StochLean source theorem: StochLean.integrableOn_variationStieltjes_of_bounded

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
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

variable {x hx hr} {f g : ℝ≥0 → ℝ} {s t : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_e21230af6e77c0b6dfe0e73f (hf : Measurable f) {C : ℝ}
    (hC : ∀ u ∈ Ioc s t, ‖f u‖ ≤ C) :
    IntegrableOn f (Ioc s t) (totalVariationStieltjes x hx hr).measure :=
  .of_bound measure_Ioc_lt_top hf.aestronglyMeasurable C
    ((ae_restrict_mem measurableSet_Ioc).mono fun u hu ↦ hC u hu)
end StochLean


