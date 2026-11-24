-- Prove2me | Definitions.Def_SourceProof_5a705a1f4d32da63ab0f4ee7
-- name    : SourceProof_5a705a1f4d32da63ab0f4ee7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:07:22.363893+00:00
-- url     : https://prove2.me/theorems/0afb219d-0adf-4f4e-bf60-45eebc6e1c37
-- title:
--   StochLean source theorem: MeasureTheory.UniformIntegrable.reindex

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
theorem _root_.Prove2MeSourceProof.h_5a705a1f4d32da63ab0f4ee7 {κ : Type*} (hX : UniformIntegrable X p P) (e : κ → ι) :
    UniformIntegrable (fun k ↦ X (e k)) p P := by
  obtain ⟨C, hC⟩ := hX.2.2
  refine ⟨fun k ↦ hX.1 (e k), ?_, C, fun k ↦ hC (e k)⟩
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hX.2.1 hε
  exact ⟨δ, hδ, fun k ↦ hδε (e k)⟩
end UniformIntegrable

end MeasureTheory


