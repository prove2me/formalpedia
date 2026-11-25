-- Prove2me | Definitions.Def_SourceProof_bfe1ba329ac07d8c42184d5a
-- name    : SourceProof_bfe1ba329ac07d8c42184d5a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:45:14.317057+00:00
-- url     : https://prove2.me/theorems/93f15c72-a4db-560f-8d32-c742e1fa55e8
-- title:
--   StochLean source theorem: StochLean.integrableOn_variationStieltjes_of_continuousOn

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left Riemann sums for pathwise Stieltjes integrals

The partial terminal cell is included, and the initial term is retained. Uniform
convergence holds on the whole horizon for continuous integrands, even when the
locally BV integrator has jumps. No nested-partition hypothesis is needed.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0}

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem _root_.Prove2MeSourceProof.h_bfe1ba329ac07d8c42184d5a {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T)) :
    IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure :=
  hf.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
    measure_Ioc_lt_top.ne
end StochLean


