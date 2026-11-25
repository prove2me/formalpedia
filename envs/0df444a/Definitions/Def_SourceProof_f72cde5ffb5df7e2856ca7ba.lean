-- Prove2me | Definitions.Def_SourceProof_f72cde5ffb5df7e2856ca7ba
-- name    : SourceProof_f72cde5ffb5df7e2856ca7ba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:49:29.173377+00:00
-- url     : https://prove2.me/theorems/34923167-d9f9-4700-bba3-2967bcd6f927
-- title:
--   StochLean source theorem: StochLean.integrableOn_variationStieltjes_leftStep

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000
import Definitions.Def_SourceProof_0b9fe09b8f4623735111204a
import Mathlib.MeasureTheory.Function.LocallyIntegrable

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

theorem _root_.Prove2MeSourceProof.h_f72cde5ffb5df7e2856ca7ba (π : TimePartition T) (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
    IntegrableOn (π.leftStep f) (Ioc 0 t) (totalVariationStieltjes x hx hr).measure :=
  _root_.Prove2MeSourceProof.h_0b9fe09b8f4623735111204a π.left π.right (fun i ↦ f (π.left i)) (f 0) t
end StochLean


