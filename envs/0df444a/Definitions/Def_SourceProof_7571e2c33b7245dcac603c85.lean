-- Prove2me | Definitions.Def_SourceProof_7571e2c33b7245dcac603c85
-- name    : SourceProof_7571e2c33b7245dcac603c85
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:53:23.786481+00:00
-- url     : https://prove2.me/theorems/3e9454a9-a867-4e2b-b4c6-38ced3089c99
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIncrementIntegral_taggedStep_terminal

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralRiemann_F000
import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
import Definitions.Def_SourceProof_b7e4a2ea52c5aed858bf1da5
import Definitions.Def_SourceProof_c1fa16da946ef4c39a6738ca
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stieltjes endpoint sums for cadlag integrands

Dominated convergence uses the actual total-variation measure on a finite
horizon. Left sums converge to the strict-left integrand and right sums to
the original integrand. These are increment integrals, without an initial atom.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0} {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem _root_.Prove2MeSourceProof.h_7571e2c33b7245dcac603c85 (π : TimePartition T)
    (ξ : Fin π.size → ℝ≥0) (f : ℝ≥0 → ℝ) :
    pathStieltjesIncrementIntegral x hx hr (π.taggedStep ξ f) 0 T =
      ∑ i : Fin π.size, f (ξ i) * π.increment x i := by
  have h := _root_.Prove2MeSourceProof.h_c1fa16da946ef4c39a6738ca (x := x) (hx := hx) (hr := hr)
    π.left π.right (fun i ↦ f (ξ i)) (_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) (f 0) T
  change StochLean.pathStieltjesIntegral x hx hr (π.taggedStep ξ f) T = _ at h
  rw [StochLean.pathStieltjesIntegral, _root_.Prove2MeSourceProof.h_b7e4a2ea52c5aed858bf1da5] at h
  apply add_left_cancel (a := f 0 * x 0)
  convert h using 1
  simp only [StochLean.TimePartition.increment, StochLean.TimePartition.left, StochLean.TimePartition.right,
    min_eq_left ((_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f π) _)]
end StochLean


