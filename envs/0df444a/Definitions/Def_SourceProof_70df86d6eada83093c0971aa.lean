-- Prove2me | Definitions.Def_SourceProof_70df86d6eada83093c0971aa
-- name    : SourceProof_70df86d6eada83093c0971aa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:37:11.904462+00:00
-- url     : https://prove2.me/theorems/d0d16413-b595-4961-88ca-9886c3aa5c93
-- title:
--   StochLean source theorem: StochLean.tendsto_quadraticVariationSum_of_cadlag_finiteVariation

import Definitions.Def_SourceProof_08d1413f21e139fa3b976ce1
import Definitions.Def_SourceProof_2910b8af6805663c425d1b72
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
import Definitions.Def_SourceProof_4d3741c5ce5f4e424b5661c4
import Definitions.Def_SourceProof_5ed481845f0350fbfacb0c3e
import Definitions.Def_SourceProof_739d7958ceaf9586a5a8a275
import Definitions.Def_SourceProof_942a1c8dc8ff80cd67f2c6e3
import Definitions.Def_SourceProof_9e7dcdf423eb929cde3bb78d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Square sums of a cadlag finite-variation path

The limit is the Stieltjes increment integral of the actual jump. The next
identification with a jump series is separate; no summability is assumed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0} {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem _root_.Prove2MeSourceProof.h_70df86d6eada83093c0971aa
    (hv : LocallyBoundedVariationOn x univ) (hc : IsCadlagPath x)
    {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ quadraticVariationSum (π n) x) atTop
      (𝓝 (pathStieltjesIncrementIntegral x hv hc.1 (fun u ↦ x u - Function.leftLim x u) 0 T)) := by
  obtain ⟨C, _, hC⟩ := (_root_.Prove2MeSourceProof.h_08d1413f21e139fa3b976ce1 hc) T
  have h := _root_.Prove2MeSourceProof.h_2910b8af6805663c425d1b72
    (x := x) (hx := hv) (hr := hc.1) (s := 0) (t := T)
    (f := fun n u ↦ (π n).taggedStep (π n).right x u - (π n).leftStep x u)
    (g := fun u ↦ x u - Function.leftLim x u) (bound := fun _ ↦ C + C)
    (fun n ↦ (((_root_.Prove2MeSourceProof.h_4d3741c5ce5f4e424b5661c4 (π n)) (π n).right x).sub
      ((_root_.Prove2MeSourceProof.h_4d3741c5ce5f4e424b5661c4 (π n)) (π n).left x)).aestronglyMeasurable)
    (integrableOn_const measure_Ioc_lt_top.ne) (fun n ↦ ?_) ?_
  · have he (n : ℕ) : StochLean.pathStieltjesIncrementIntegral x hv hc.1
        (fun u ↦ (π n).taggedStep (π n).right x u - (π n).leftStep x u) 0 T =
        StochLean.quadraticVariationSum (π n) x :=
      _root_.Prove2MeSourceProof.h_5ed481845f0350fbfacb0c3e (hx := hv) (hr := hc.1) (π n)
    simpa only [he] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (norm_sub_le _ _).trans (add_le_add
      ((_root_.Prove2MeSourceProof.h_9e7dcdf423eb929cde3bb78d (π n)) (π n).right
        (fun i ↦ ⟨bot_le, (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) _⟩) hC ⟨hu.1.le, hu.2⟩)
      ((_root_.Prove2MeSourceProof.h_9e7dcdf423eb929cde3bb78d (π n)) (π n).left
        (fun i ↦ ⟨bot_le, (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) _⟩) hC ⟨hu.1.le, hu.2⟩))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (_root_.Prove2MeSourceProof.h_942a1c8dc8ff80cd67f2c6e3 hu (hc.1 u) hmesh).sub
      (_root_.Prove2MeSourceProof.h_739d7958ceaf9586a5a8a275 hu
        (tendsto_leftLim_of_tendsto (hc.2 u (ne_of_gt hu.1))) hmesh)
end StochLean


