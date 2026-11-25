-- Prove2me | Definitions.Def_SourceProof_a7b3cca34d6b43059ea19d62
-- name    : SourceProof_a7b3cca34d6b43059ea19d62
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:24.732986+00:00
-- url     : https://prove2.me/theorems/f8e794b1-651e-411d-9d9f-db7ae038b31d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSquareIntegrableMartingale.indicator_initial

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_SourceProof_208de2e405fcede8b8f859e6

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial masking and stability of finite-time L2 martingales

The stable local property includes common-event cadlag paths. No global second
moment bound is introduced.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory.Martingale

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSquareIntegrableMartingale
theorem _root_.Prove2MeSourceProof.h_a7b3cca34d6b43059ea19d62
    (hX : IsSquareIntegrableMartingale X F P) {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    IsSquareIntegrableMartingale (fun t ↦ s.indicator (X t)) F P :=
  ⟨(_root_.Prove2MeSourceProof.h_208de2e405fcede8b8f859e6 hX.1) hs, fun t ↦ (hX.2 t).indicator (F.le 0 s hs)⟩
end IsSquareIntegrableMartingale

end ProbabilityTheory


