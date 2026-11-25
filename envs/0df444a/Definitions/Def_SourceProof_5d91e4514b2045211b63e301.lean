-- Prove2me | Definitions.Def_SourceProof_5d91e4514b2045211b63e301
-- name    : SourceProof_5d91e4514b2045211b63e301
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:50:44.712413+00:00
-- url     : https://prove2.me/theorems/47fc65bb-52e0-5a94-b686-cdea5af5d86f
-- title:
--   StochLean source theorem: StochLean.TimePartition.tendsto_endpointPairStep_of_cadlag

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_59527d7a236691596fcf380b
import Definitions.Def_SourceProof_7ebcdf415b376e81ffc593ac
import Definitions.Def_SourceProof_8f7895612117943074291d58
import Definitions.Def_SourceProof_eceb36ff6d0faabf53b4693c
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite steps depending on both cell endpoint values

Repeated endpoints are allowed. At positive times the unique nonempty cell
determines both values; the initial value is retained separately.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

namespace TimePartition

variable {T : ℝ≥0} {E : Type*}

theorem _root_.Prove2MeSourceProof.h_5d91e4514b2045211b63e301 [MetricSpace E] {π : ℕ → TimePartition T}
    {Φ : E → E → ℝ} (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2))
    {x : ℝ≥0 → E} (hx : IsCadlagPath x) {t : ℝ≥0} (ht : t ∈ Ioc 0 T)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (π n).endpointPairStep Φ x t) atTop
      (𝓝 (Φ (Function.leftLim x t) (x t))) := by
  choose i hi using fun n ↦ (_root_.Prove2MeSourceProof.h_8f7895612117943074291d58 (π n)) ht
  have hl : Tendsto (fun n ↦ (π n).left (i n)) atTop (𝓝[<] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n ↦ (hi n).1⟩
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) hmesh
    simpa only [dist_comm] using (_root_.Prove2MeSourceProof.h_7ebcdf415b376e81ffc593ac (π n)) (hi n)
  have hr : Tendsto (fun n ↦ (π n).right (i n)) atTop (𝓝[≥] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n ↦ (hi n).2⟩
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) hmesh
    simpa only [dist_comm] using (_root_.Prove2MeSourceProof.h_59527d7a236691596fcf380b (π n)) (π n).right
      (fun j ↦ ⟨(_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (π n)) j, le_rfl⟩) (hi n)
  have hxl := (tendsto_leftLim_of_tendsto (hx.2 t (ne_of_gt ht.1))).comp hl
  have hxr := (hx.1 t).tendsto.comp hr
  simpa only [fun n ↦ (_root_.Prove2MeSourceProof.h_eceb36ff6d0faabf53b4693c (π n)) Φ x (hi n),
    Function.comp_def] using
    (hΦ.tendsto (Function.leftLim x t, x t)).comp (hxl.prodMk_nhds hxr)
end TimePartition

variable {T : ℝ≥0} {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

end StochLean


