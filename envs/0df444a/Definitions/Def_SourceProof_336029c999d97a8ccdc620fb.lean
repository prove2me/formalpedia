-- Prove2me | Definitions.Def_SourceProof_336029c999d97a8ccdc620fb
-- name    : SourceProof_336029c999d97a8ccdc620fb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:37.809578+00:00
-- url     : https://prove2.me/theorems/38b33220-252e-4132-8bc1-8a467dc483b1
-- title:
--   StochLean source theorem: ProbabilityTheory.tendsto_measure_le_of_ae_tendsto_top

import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Vanishing probabilities of early localization

AE divergence of a pre-localizing sequence already suffices. Monotonicity is not needed
for the probability estimate.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {τ : ℕ → Ω → WithTop ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_336029c999d97a8ccdc620fb (hm : ∀ n, Measurable (τ n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ τ n ω) atTop (𝓝 ⊤))
    (T : ℝ≥0) : Tendsto (fun n ↦ P {ω | τ n ω ≤ T}) atTop (𝓝 0) := by
  have he : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ {ω | τ n ω ≤ T} ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hlim] with ω hω
    filter_upwards [hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))] with n hn
    simp only [mem_empty_iff_false, iff_false]
    exact not_le.mpr hn
  simpa only [measure_empty] using
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty
      (fun n ↦ measurableSet_le (hm n) measurable_const) he
end ProbabilityTheory


