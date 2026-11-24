-- Prove2me | Definitions.Def_SourceProof_4f067a71c20982dfbf53ab5f
-- name    : SourceProof_4f067a71c20982dfbf53ab5f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:20.424926+00:00
-- url     : https://prove2.me/theorems/abe914a9-ae78-4957-a875-c658f39e705b
-- title:
--   StochLean source theorem: ProbabilityTheory.tendsto_compactDeviation_mul_right

import Definitions.Def_SourceProof_35d9cd8d11b1180665dd91a3

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # UCP multiplication by a fixed caglad process

The multiplier need only be pathwise bounded on compact intervals, not bounded
uniformly in the sample point or integrable. Countable dense deviations provide
the needed measurability, including an independent initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_4f067a71c20982dfbf53ab5f {ι : Type*} {l : Filter ι}
    {Z : ι → ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω}
    (hu : Tendsto (fun n ↦ compactDeviation (Z n) Y T ω) l (𝓝 0))
    (hH : ∃ C : ℝ, ∀ t ≤ T, ‖H t ω‖ ≤ C) :
    Tendsto (fun n ↦ compactDeviation (Z n * H) (Y * H) T ω) l (𝓝 0) := by
  obtain ⟨C, hC⟩ := hH
  have hb := ENNReal.Tendsto.mul_const hu (Or.inr (ENNReal.ofReal_ne_top :
    ENNReal.ofReal C ≠ ∞))
  rw [zero_mul] at hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ ↦ bot_le) (fun _ ↦ _root_.Prove2MeSourceProof.h_35d9cd8d11b1180665dd91a3 hC)
end ProbabilityTheory


