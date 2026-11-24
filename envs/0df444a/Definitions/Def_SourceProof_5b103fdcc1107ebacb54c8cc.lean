-- Prove2me | Definitions.Def_SourceProof_5b103fdcc1107ebacb54c8cc
-- name    : SourceProof_5b103fdcc1107ebacb54c8cc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:46.266871+00:00
-- url     : https://prove2.me/theorems/e77e3f09-a961-48c7-a891-dd8f50fa3efe
-- title:
--   StochLean source theorem: ProbabilityTheory.isGoodIntegrator_of_ae_elementaryIntegral_bound

import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adapted cadlag finite-variation processes are semimartingales

Protter II.7 follows directly from the pathwise elementary-integral bound. The random
variation need not be integrable. This does not yet construct a Stieltjes measure or the
general Chapter II integral.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_5b103fdcc1107ebacb54c8cc (R : Ω → ℝ)
    (hmeas : ∀ H : ℝ≥0 → Ω → ℝ, ∀ hH : IsSimplePredictable H F,
      AEStronglyMeasurable (hH.elementaryIntegral X) P)
    (hb : ∀ᵐ ω ∂P, 0 ≤ R ω ∧
      ∀ H : ℝ≥0 → Ω → ℝ, ∀ hH : IsSimplePredictable H F, ∀ C : ℝ, 0 ≤ C →
        (∀ t ω, ‖H t ω‖ ≤ C) → ‖hH.elementaryIntegral X ω‖ ≤ C * R ω) :
    IsGoodIntegrator X F P := by
  intro H hH hu
  apply tendstoInMeasure_of_tendsto_ae (fun n ↦ hmeas (H n) (hH n))
  filter_upwards [hb] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hδ : 0 < ε / (R ω + 1) := div_pos hε (by linarith [hω.1])
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hu _ hδ)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hbound : ∀ t v, ‖H n t v‖ ≤ ε / (R ω + 1) := by
    intro t v
    simpa only [dist_zero_left] using (hN n hn (t, v)).le
  have h := hω.2 (H n) (hH n) _ hδ.le hbound
  change dist ((hH n).elementaryIntegral X ω) 0 < ε
  rw [dist_zero_right]
  apply h.trans_lt
  have heq : ε / (R ω + 1) * (R ω + 1) = ε := div_mul_cancel₀ ε (by linarith [hω.1])
  nlinarith
end ProbabilityTheory


