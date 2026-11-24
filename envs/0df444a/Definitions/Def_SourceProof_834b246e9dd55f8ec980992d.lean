-- Prove2me | Definitions.Def_SourceProof_834b246e9dd55f8ec980992d
-- name    : SourceProof_834b246e9dd55f8ec980992d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:49.311188+00:00
-- url     : https://prove2.me/theorems/25100dc1-3328-43f9-8215-055406050480
-- title:
--   StochLean source theorem: MeasureTheory.UniformIntegrable.indicator

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
theorem _root_.Prove2MeSourceProof.h_834b246e9dd55f8ec980992d (hX : UniformIntegrable X p P)
    {s : Set Ω} (hs : MeasurableSet s) :
    UniformIntegrable (fun t ↦ s.indicator (X t)) p P := by
  obtain ⟨C, hC⟩ := hX.2.2
  exact ⟨fun t ↦ (hX.1 t).indicator hs, hX.2.1.indicator s,
    C, fun t ↦ (eLpNorm_indicator_le _).trans (hC t)⟩
end UniformIntegrable

end MeasureTheory


