-- Prove2me | Definitions.Def_SourceProof_557b326145f3a25cf73cd318
-- name    : SourceProof_557b326145f3a25cf73cd318
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:18.723869+00:00
-- url     : https://prove2.me/theorems/3e6505ef-1fac-4983-996f-d43af67b81a7
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.reindex

import Definitions.Def_StochLean_Probability_Process_Filtration_Reindex_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Deterministic monotone reindexing of filtrations and martingales -/

@[expose] public section

namespace MeasureTheory

variable {Ω ι κ E : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι] [Preorder κ]

namespace Martingale
theorem _root_.Prove2MeSourceProof.h_557b326145f3a25cf73cd318 [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Filtration ι mΩ} {P : Measure Ω} {X : ι → Ω → E} (hX : Martingale X F P)
    (e : κ → ι) (he : Monotone e) : Martingale (fun k ↦ X (e k)) (F.reindex e he) P :=
  ⟨fun k ↦ hX.stronglyAdapted (e k), fun _ _ h ↦ hX.condExp_ae_eq (he h)⟩
end Martingale

end MeasureTheory


