-- Prove2me | Definitions.Def_SourceProof_0feb9d2237bb25262c913342
-- name    : SourceProof_0feb9d2237bb25262c913342
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:26:18.024854+00:00
-- url     : https://prove2.me/theorems/a5294548-8a1e-58ef-b9b3-b39ad0d4998e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.masked_stoppedProcess

import Definitions.Def_SourceProof_2c97b0da88fd3eb21715f5f0
import Definitions.Def_SourceProof_6c3d8ad2cd18b3f669ebceea
import Definitions.Def_SourceProof_e79cc5d7fc8aa48d10e205ad

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Reducing times and initial-event masking: Protter I.48(a,c,d) -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

namespace IsLocalMartingale
theorem _root_.Prove2MeSourceProof.h_0feb9d2237bb25262c913342 (hX : IsLocalMartingale X F P)
    (hF : F.IsUsual P) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsLocalMartingale (MeasureTheory.stoppedProcess
      (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) F P := by
  have hs : MeasurableSet[F 0] {ω | 0 < τ ω} := by
    simpa only [WithTop.coe_zero, Set.compl_ofPred, not_le] using (hτ 0).compl
  exact (_root_.Prove2MeSourceProof.h_2c97b0da88fd3eb21715f5f0 ((_root_.Prove2MeSourceProof.h_6c3d8ad2cd18b3f669ebceea hX) hs)) hF hτ
end IsLocalMartingale

end ProbabilityTheory


