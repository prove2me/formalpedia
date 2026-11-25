-- Prove2me | Definitions.Def_SourceProof_c3eab2187d68c022ae90ef4e
-- name    : SourceProof_c3eab2187d68c022ae90ef4e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:32:32.088664+00:00
-- url     : https://prove2.me/theorems/5bc74f49-ff3a-4b43-b842-7ec051c924cb
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIntegral_leftStep

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralRiemann_F000
import Definitions.Def_SourceProof_c1fa16da946ef4c39a6738ca
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

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

theorem _root_.Prove2MeSourceProof.h_c3eab2187d68c022ae90ef4e (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    pathStieltjesIntegral x hx hr (π.leftStep f) = stieltjesLeftSum π x f := by
  funext t
  exact _root_.Prove2MeSourceProof.h_c1fa16da946ef4c39a6738ca π.left π.right (fun i ↦ f (π.left i))
    (_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) (f 0) t
end StochLean


