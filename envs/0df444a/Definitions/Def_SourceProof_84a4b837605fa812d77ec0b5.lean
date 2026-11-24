-- Prove2me | Definitions.Def_SourceProof_84a4b837605fa812d77ec0b5
-- name    : SourceProof_84a4b837605fa812d77ec0b5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:42.355998+00:00
-- url     : https://prove2.me/theorems/904ae61c-2340-4438-97d9-92e794cff904
-- title:
--   StochLean source theorem: MeasureTheory.UniformIntegrable.add

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
theorem _root_.Prove2MeSourceProof.h_84a4b837605fa812d77ec0b5 (hX : UniformIntegrable X p P)
    (hY : UniformIntegrable Y p P) (hp : 1 ≤ p) :
    UniformIntegrable (X + Y) p P := by
  obtain ⟨C, hC⟩ := hX.2.2
  obtain ⟨D, hD⟩ := hY.2.2
  refine ⟨fun t ↦ (hX.1 t).add (hY.1 t),
    hX.2.1.add hY.2.1 hp hX.1 hY.1, C + D, fun t ↦ ?_⟩
  exact (eLpNorm_add_le (hX.1 t) (hY.1 t) hp).trans (by
    simpa only [ENNReal.coe_add] using add_le_add (hC t) (hD t))
end UniformIntegrable

end MeasureTheory


