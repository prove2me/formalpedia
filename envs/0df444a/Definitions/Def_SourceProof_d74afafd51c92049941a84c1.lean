-- Prove2me | Definitions.Def_SourceProof_d74afafd51c92049941a84c1
-- name    : SourceProof_d74afafd51c92049941a84c1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:20.134806+00:00
-- url     : https://prove2.me/theorems/59e4abed-fb1c-517f-8070-8832b5372e79
-- title:
--   StochLean source theorem: StochLean.locallyBoundedVariationOn_tprod_Ioc

import Definitions.Def_SourceProof_67e31fd87e2ed1febfe45404
import Definitions.Def_SourceProof_802c352df5798861ebae9666
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

theorem _root_.Prove2MeSourceProof.h_d74afafd51c92049941a84c1 {f : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |f s - 1|)) :
    LocallyBoundedVariationOn (fun t : ℝ≥0 ↦ ∏' s : Ioc 0 t, f s) univ := by
  classical
  intro a b ha hb
  let A : ℝ≥0 → Set (Ioc (0 : ℝ≥0) b) := fun t ↦ {s | (s : ℝ≥0) ≤ t}
  have hA : Monotone A := fun _ _ htu _ hs ↦ hs.trans htu
  have hv := _root_.Prove2MeSourceProof.h_67e31fd87e2ed1febfe45404
    (w := fun s : Ioc 0 b ↦ f s - 1) hA (hs b)
  have he (t : ℝ≥0) :
      (∏' s : Ioc 0 b, (A t).mulIndicator (fun s ↦ 1 + (f s - 1)) s) =
        ∏' s : Ioc 0 (min b t), f s := by
    convert _root_.Prove2MeSourceProof.h_802c352df5798861ebae9666 f t b using 1
    apply tprod_congr
    intro s
    simp only [Set.mulIndicator, A, mem_ofPred_eq, add_sub_cancel]
  have hvab := hv a b ha hb
  change eVariationOn _ _ ≠ ⊤ at hvab ⊢
  rw [eVariationOn.eq_of_eqOn (f' := fun t : ℝ≥0 ↦ ∏' s : Ioc 0 t, f s) (by
    intro t ht
    change (∏' s : Ioc 0 b, (A t).mulIndicator (fun s ↦ 1 + (f s - 1)) s) = _
    rw [he, min_eq_right ht.2.2])] at hvab
  exact hvab
end StochLean


