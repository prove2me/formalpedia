-- Prove2me | Definitions.Def_SourceProof_67e31fd87e2ed1febfe45404
-- name    : SourceProof_67e31fd87e2ed1febfe45404
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:37.055454+00:00
-- url     : https://prove2.me/theorems/981b4574-5698-53e3-865c-fea1e465daee
-- title:
--   StochLean source theorem: StochLean.locallyBoundedVariationOn_tprod_monotone_cutoff

import Definitions.Def_SourceProof_8fd5626f1050c626fa529bb3
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Local finite variation of absolutely convergent cumulative products

Expanding the product over finite subsets expresses it as an absolutely
convergent sum. Every subset coefficient is activated at most once as
time increases. This proves finite variation without taking logarithms,
excluding zero factors, or assuming positivity.
-/

@[expose] public section

open Set
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_67e31fd87e2ed1febfe45404
    {α ι : Type*} [LinearOrder α] {a : α → Set ι} (ha : Monotone a)
    {w : ι → ℝ} (hw : Summable (fun i ↦ |w i|)) :
    LocallyBoundedVariationOn
      (fun t ↦ ∏' i, (a t).mulIndicator (fun i ↦ 1 + w i) i) univ := by
  classical
  let W : Finset ι → ℝ := fun s ↦ ∏ i ∈ s, w i
  let A : α → Set (Finset ι) := fun t ↦ {s | ∀ i ∈ s, i ∈ a t}
  have hA : Monotone A := fun _ _ hst _ hs i hi ↦ ha hst (hs i hi)
  have hW : Summable (fun s ↦ |W s|) :=
    (summable_finsetProd_of_summable_norm hw.of_abs.norm).abs
  have hv := _root_.Prove2MeSourceProof.h_8fd5626f1050c626fa529bb3 (w := W) hA hW
  have he (t : α) : (∏' i, (a t).mulIndicator (fun i ↦ 1 + w i) i) =
      ∑' s, (A t).indicator W s := by
    have hg : Summable (fun i ↦ ‖(a t).indicator w i‖) :=
      (hw.of_abs.indicator (a t)).norm
    convert tprod_one_add (summable_finsetProd_of_summable_norm hg) using 1
    · apply tprod_congr
      intro i
      by_cases hi : i ∈ a t <;> simp [Set.mulIndicator, Set.indicator, hi]
    · apply tsum_congr
      intro s
      simp only [Set.indicator, Finset.prod_ite_zero, A, mem_ofPred_eq, W]
  simpa only [← he] using hv
end StochLean


