-- Prove2me | Definitions.Def_SourceProof_09dae940366568ba50883f76
-- name    : SourceProof_09dae940366568ba50883f76
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:13.559645+00:00
-- url     : https://prove2.me/theorems/6dc640f4-819c-49f3-a7fa-12f95eb0cf2b
-- title:
--   StochLean source theorem: StochLean.stieltjesLeftSum_terminal

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralRiemann_F000
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f

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

theorem _root_.Prove2MeSourceProof.h_09dae940366568ba50883f76 (π : TimePartition T) (x f : ℝ≥0 → ℝ) :
    stieltjesLeftSum π x f T = f 0 * x 0 + ∑ i : Fin π.size, f (π.left i) * π.increment x i := by
  simp only [StochLean.stieltjesLeftSum, TimePartition.increment, StochLean.TimePartition.left, StochLean.TimePartition.right,
    min_eq_left ((_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f π) _)]
variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

end StochLean


