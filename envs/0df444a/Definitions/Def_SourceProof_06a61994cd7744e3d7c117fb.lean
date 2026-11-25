-- Prove2me | Definitions.Def_SourceProof_06a61994cd7744e3d7c117fb
-- name    : SourceProof_06a61994cd7744e3d7c117fb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:08:40.219205+00:00
-- url     : https://prove2.me/theorems/12920dc9-ab16-434c-8e63-472842a2e64b
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.eTotalVariationProcess_of_rightContinuous

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Variation_F000
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
import Definitions.Def_SourceProof_36da4c661fc115cbdc2bfff4
import Definitions.Def_SourceProof_445d46fbf60cf5615d2de765
import Definitions.Def_SourceProof_8103132b28acf1a349b559b2
import Definitions.Def_SourceProof_f0d7366f281cd44e7eb0e371

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The adapted total-variation process

Variation is first kept in ENNReal, including infinite values. Right continuity,
not continuity, makes actual finite-partition sums converge to it. Real-valued
variation is the canonical Mathlib conversion; its finite-variation interpretation
requires the common-event locally BV hypothesis.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_06a61994cd7744e3d7c117fb (ha : Adapted F X)
    (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω)) :
    Adapted F (ProbabilityTheory.eTotalVariationProcess X) := by
  intro T
  let π : ℕ → StochLean.TimePartition T := fun n ↦ (StochLean.LocallyFinitePartition.dyadic n).restrict T
  have hm : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      ((_root_.Prove2MeSourceProof.h_f0d7366f281cd44e7eb0e371 _root_.Prove2MeSourceProof.h_36da4c661fc115cbdc2bfff4) (fun _ ↦ T))
  let : MeasurableSpace Ω := F T
  change Measurable (fun ω ↦ ProbabilityTheory.eTotalVariationProcess X T ω)
  apply measurable_of_tendsto_metrizable
    (f := fun n ω ↦ ENNReal.ofReal (StochLean.pVariationSum 1 (π n) (fun t ↦ X t ω)))
  · intro n
    apply ENNReal.measurable_ofReal.comp
    simp only [_root_.Prove2MeSourceProof.h_445d46fbf60cf5615d2de765]
    apply Finset.measurable_fun_sum
    intro i _
    have hd : Measurable (fun ω ↦ X ((π n).right i) ω - X ((π n).left i) ω) :=
      ((ha _).mono (F.mono ((_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) i.succ)) le_rfl).sub
        ((ha _).mono (F.mono ((_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) i.castSucc)) le_rfl)
    simpa only [Real.norm_eq_abs, StochLean.TimePartition.increment] using hd.norm
  · apply tendsto_pi_nhds.mpr
    intro ω
    exact _root_.Prove2MeSourceProof.h_8103132b28acf1a349b559b2 (hr ω) hm
end Adapted

end MeasureTheory


