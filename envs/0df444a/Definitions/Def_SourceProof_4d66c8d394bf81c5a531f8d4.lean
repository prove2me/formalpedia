-- Prove2me | Definitions.Def_SourceProof_4d66c8d394bf81c5a531f8d4
-- name    : SourceProof_4d66c8d394bf81c5a531f8d4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:08:04.516797+00:00
-- url     : https://prove2.me/theorems/09feda6f-e714-4a26-bc8b-c210a8cf6e02
-- title:
--   StochLean source theorem: MeasureTheory.UniformIntegrable.mono_norm

import Mathlib.MeasureTheory.Function.UniformIntegrable

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Operations on uniformly integrable families -/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] {X Y : ι → Ω → E} {p : ℝ≥0∞}

namespace UniformIntegrable

theorem _root_.Prove2MeSourceProof.h_4d66c8d394bf81c5a531f8d4 (hY : UniformIntegrable Y p P)
    (hX : ∀ i, AEStronglyMeasurable (X i) P)
    (hXY : ∀ i, ∀ᵐ ω ∂P, ‖X i ω‖ ≤ ‖Y i ω‖) : UniformIntegrable X p P := by
  obtain ⟨C, hC⟩ := hY.2.2
  refine ⟨hX, ?_, C, fun i ↦ (eLpNorm_mono_ae (hXY i)).trans (hC i)⟩
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hY.2.1 hε
  refine ⟨δ, hδ, fun i s hs hPs ↦ ?_⟩
  apply le_trans (eLpNorm_mono_ae ?_) (hδε i s hs hPs)
  filter_upwards [hXY i] with ω hω
  by_cases hmem : ω ∈ s <;> simp [hmem, hω]
end UniformIntegrable

end MeasureTheory


