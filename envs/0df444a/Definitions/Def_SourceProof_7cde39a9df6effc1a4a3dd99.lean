-- Prove2me | Definitions.Def_SourceProof_7cde39a9df6effc1a4a3dd99
-- name    : SourceProof_7cde39a9df6effc1a4a3dd99
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:28.491332+00:00
-- url     : https://prove2.me/theorems/fb29db5c-d282-4a34-b053-f3a269ae56c9
-- title:
--   StochLean source theorem: ProbabilityTheory.IsKlenkeLocalizingSequence.isFundamentalSequence

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_SourceProof_5ac3f4c5fe22f7841ec0a6bc

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
theorem _root_.Prove2MeSourceProof.h_7cde39a9df6effc1a4a3dd99
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsKlenkeLocalizingSequence X F P τ) :
    IsFundamentalSequence X F P τ := by
  refine ⟨hτ.1, hτ.2.1, fun n ↦ ?_⟩
  have hs : MeasurableSet[F 0] {ω | 0 < τ n ω} := by
    simpa only [WithTop.coe_zero, Set.compl_ofPred, not_le] using
      (hτ.1.isStoppingTime n 0).compl
  simpa only [stoppedProcess_indicator_comm'] using (_root_.Prove2MeSourceProof.h_5ac3f4c5fe22f7841ec0a6bc (hτ.2.2 n)) hs
end IsKlenkeLocalizingSequence

end ProbabilityTheory


