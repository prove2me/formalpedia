-- Prove2me | Definitions.Def_SourceProof_a62252018268fa29cedecd73
-- name    : SourceProof_a62252018268fa29cedecd73
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:29:02.701463+00:00
-- url     : https://prove2.me/theorems/43068a0c-0dfe-4c28-ab72-f463b6064218
-- title:
--   StochLean source theorem: StochLean.tendsto_stieltjesIncrementLeftSum_of_cadlag

import Definitions.Def_SourceProof_08d1413f21e139fa3b976ce1
import Definitions.Def_SourceProof_2910b8af6805663c425d1b72
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
import Definitions.Def_SourceProof_4d3741c5ce5f4e424b5661c4
import Definitions.Def_SourceProof_739d7958ceaf9586a5a8a275
import Definitions.Def_SourceProof_9e21fcad2fff4622240860ee
import Definitions.Def_SourceProof_9e7dcdf423eb929cde3bb78d

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

theorem _root_.Prove2MeSourceProof.h_a62252018268fa29cedecd73 {π : ℕ → TimePartition T}
    {f : ℝ≥0 → ℝ} (hf : IsCadlagPath f)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i : Fin (π n).size, f ((π n).left i) * (π n).increment x i) atTop
      (𝓝 (pathStieltjesIncrementIntegral x hx hr (Function.leftLim f) 0 T)) := by
  obtain ⟨C, _, hC⟩ := (_root_.Prove2MeSourceProof.h_08d1413f21e139fa3b976ce1 hf) T
  have h := _root_.Prove2MeSourceProof.h_2910b8af6805663c425d1b72
    (x := x) (hx := hx) (hr := hr) (s := 0) (t := T) (f := fun n ↦ (π n).leftStep f)
    (g := Function.leftLim f) (bound := fun _ ↦ C)
    (fun n ↦ ((_root_.Prove2MeSourceProof.h_4d3741c5ce5f4e424b5661c4 (π n)) (π n).left f).aestronglyMeasurable)
    (integrableOn_const measure_Ioc_lt_top.ne) (fun n ↦ ?_) ?_
  · simpa only [_root_.Prove2MeSourceProof.h_9e21fcad2fff4622240860ee] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (_root_.Prove2MeSourceProof.h_9e7dcdf423eb929cde3bb78d (π n)) (π n).left
      (fun i ↦ ⟨bot_le, (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) _⟩) hC ⟨hu.1.le, hu.2⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact _root_.Prove2MeSourceProof.h_739d7958ceaf9586a5a8a275 hu
      (tendsto_leftLim_of_tendsto (hf.2 u (ne_of_gt hu.1))) hmesh
end StochLean


