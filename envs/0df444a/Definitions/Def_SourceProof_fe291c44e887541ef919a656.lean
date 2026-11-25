-- Prove2me | Definitions.Def_SourceProof_fe291c44e887541ef919a656
-- name    : SourceProof_fe291c44e887541ef919a656
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:22:25.502014+00:00
-- url     : https://prove2.me/theorems/5ddcf5d6-e431-51e9-937d-dedda3443283
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.add

import Definitions.Def_SourceProof_84a4b837605fa812d77ec0b5
import Definitions.Def_SourceProof_c723bba90ef663ed2d82d1f9
import Definitions.Def_SourceProof_f27f0406d0856e73dc290674

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Stopping and linear stability of Protter local martingales

Fundamental sequences are actual witnesses. A shared localizer is the pointwise
minimum of two existing localizers. Its time-zero mask is the intersection of
their masks; the unmasked Klenke definition is not silently substituted.

Source: Protter I.48 (stopping and linear operations).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

namespace IsLocalMartingale
theorem _root_.Prove2MeSourceProof.h_fe291c44e887541ef919a656 (hX : IsLocalMartingale X F P)
    (hY : IsLocalMartingale Y F P) (hF : F.IsUsual P) :
    IsLocalMartingale (X + Y) F P := by
  obtain ⟨τ, hτ⟩ := hX.2.2
  obtain ⟨σ, hσ⟩ := hY.2.2
  have hx := (_root_.Prove2MeSourceProof.h_c723bba90ef663ed2d82d1f9 hτ) hX.2.1 hF hσ.1 hσ.2.1
  have hy := (_root_.Prove2MeSourceProof.h_c723bba90ef663ed2d82d1f9 hσ) hY.2.1 hF hτ.1 hτ.2.1
  rw [inf_comm σ τ] at hy
  refine ⟨hX.1.add hY.1, (_root_.Prove2MeSourceProof.h_f27f0406d0856e73dc290674 hX.2.1) hY.2.1, min τ σ, hx.1, hx.2.1, fun n ↦ ?_⟩
  have hsum : ProbabilityTheory.IsUIMartingale
      ((MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < min τ σ n ω}.indicator (X t))
        (min τ σ n)) +
       (MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < min τ σ n ω}.indicator (Y t))
        (min τ σ n))) F P :=
      ⟨(hx.2.2 n).1.add (hy.2.2 n).1, (_root_.Prove2MeSourceProof.h_84a4b837605fa812d77ec0b5 (hx.2.2 n).2) (hy.2.2 n).2 le_rfl⟩
  convert hsum using 1
  ext t ω
  rw [Pi.add_apply, Pi.add_apply, stoppedProcess_indicator_comm,
    stoppedProcess_indicator_comm, stoppedProcess_indicator_comm]
  simp only [stoppedProcess_add, Pi.add_apply, Set.indicator_add']
end IsLocalMartingale

end ProbabilityTheory


