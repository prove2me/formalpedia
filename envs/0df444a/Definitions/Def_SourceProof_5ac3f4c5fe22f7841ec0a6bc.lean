-- Prove2me | Definitions.Def_SourceProof_5ac3f4c5fe22f7841ec0a6bc
-- name    : SourceProof_5ac3f4c5fe22f7841ec0a6bc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:24.375721+00:00
-- url     : https://prove2.me/theorems/696d602d-0004-4cdc-aff6-88041cebad97
-- title:
--   StochLean source theorem: ProbabilityTheory.IsUIMartingale.indicator_initial

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_SourceProof_834b246e9dd55f8ec980992d

open private martingale_indicator_initial from Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Protter local martingales and Klenke localization

The canonical local martingale uses masked stopped UI martingales (Protter I.6).
Klenke's unmasked localizer is witness data, not a competing process hierarchy.
The unmasked bridge requires integrability of the initial value. Time is `ℝ≥0`;
stopping times have values in `WithTop ℝ≥0`, and stopped processes are only
evaluated at finite deterministic times.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsUIMartingale
theorem _root_.Prove2MeSourceProof.h_5ac3f4c5fe22f7841ec0a6bc (hX : IsUIMartingale X F P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    IsUIMartingale (fun t ↦ s.indicator (X t)) F P :=
  ⟨martingale_indicator_initial hX.1 hs, (_root_.Prove2MeSourceProof.h_834b246e9dd55f8ec980992d hX.2) (F.le 0 s hs)⟩
end IsUIMartingale

end ProbabilityTheory


