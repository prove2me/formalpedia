-- Prove2me | Definitions.Def_StochLean_Probability_Process_Filtration_Reindex_F000
-- name    : StochLean_Probability_Process_Filtration_Reindex_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:44.533456+00:00
-- url     : https://prove2.me/theorems/beb5513e-0a7f-4ed8-9305-a13c68f53dea
-- title:
--   Monotone reindexing of filtrations
-- statement:
--   A monotone map between ordered time sets induces a filtration by composition with the original filtration.

import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Deterministic monotone reindexing of filtrations and martingales -/

@[expose] public section

namespace MeasureTheory

variable {Ω ι κ E : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι] [Preorder κ]

def Filtration.reindex (F : Filtration ι mΩ) (e : κ → ι) (he : Monotone e) :
    Filtration κ mΩ :=
  ⟨fun k ↦ F (e k), fun _ _ h ↦ F.mono (he h), fun k ↦ F.le (e k)⟩
end MeasureTheory


