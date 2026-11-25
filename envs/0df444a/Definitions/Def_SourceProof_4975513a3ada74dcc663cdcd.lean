-- Prove2me | Definitions.Def_SourceProof_4975513a3ada74dcc663cdcd
-- name    : SourceProof_4975513a3ada74dcc663cdcd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:54.542798+00:00
-- url     : https://prove2.me/theorems/3fe413dd-c089-40e0-9179-7b883c3cdcbc
-- title:
--   StochLean source theorem: ProbabilityTheory.IsKlenkeLocalizingSequence.isLocalMartingale

import Definitions.Def_SourceProof_7cde39a9df6effc1a4a3dd99

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

namespace IsKlenkeLocalizingSequence
theorem _root_.Prove2MeSourceProof.h_4975513a3ada74dcc663cdcd
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsKlenkeLocalizingSequence X F P τ)
    (hadapt : Adapted F X) (hcad : HasCadlagPaths X P) : IsLocalMartingale X F P :=
  ⟨hadapt, hcad, τ, (_root_.Prove2MeSourceProof.h_7cde39a9df6effc1a4a3dd99 hτ)⟩
end IsKlenkeLocalizingSequence

end ProbabilityTheory


