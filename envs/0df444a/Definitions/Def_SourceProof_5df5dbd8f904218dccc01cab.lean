-- Prove2me | Definitions.Def_SourceProof_5df5dbd8f904218dccc01cab
-- name    : SourceProof_5df5dbd8f904218dccc01cab
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:51:52.414576+00:00
-- url     : https://prove2.me/theorems/5731f01d-3a0b-4049-9739-1bf3bb4dae8c
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isLocalizingSequence_cappedNormExitSequence

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_CadlagExitLocalization_F000
import Definitions.Def_SourceProof_6e6c0736914066f88cc333e2
import Definitions.Def_SourceProof_c2cc59834fa00d679453bf21
import Definitions.Def_SourceProof_d27c5b9383fd22e9caafc8fd

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Capped open norm exits for cadlag localization

The stopping sequence is the existing open norm hit, capped by its increasing
integer threshold. Cadlag compact bounds imply divergence. Strictly before
the exit, the path is bounded by the threshold, and the same bound holds for
its left limit at the exit. A bound on positive-time jumps controls overshoot.

Without a jump bound the stopped process is not claimed to be bounded. Only
its jumps away from the stopping endpoint are at most twice the threshold;
the non-strict inequality and the exceptional endpoint are retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_5df5dbd8f904218dccc01cab
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    IsLocalizingSequence F (cappedNormExitSequence X) P :=
  ⟨⟨fun n ↦ (_root_.Prove2MeSourceProof.h_6e6c0736914066f88cc333e2 ha) hF hc n,
    (_root_.Prove2MeSourceProof.h_c2cc59834fa00d679453bf21 hc)⟩,
    Eventually.of_forall fun ω _n _m hnm ↦ _root_.Prove2MeSourceProof.h_d27c5b9383fd22e9caafc8fd X hnm ω⟩
end Adapted

end MeasureTheory


