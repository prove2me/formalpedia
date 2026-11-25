-- Prove2me | Definitions.Def_SourceProof_6e6c0736914066f88cc333e2
-- name    : SourceProof_6e6c0736914066f88cc333e2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:41:19.680294+00:00
-- url     : https://prove2.me/theorems/155b6d28-9698-4ad3-adbb-70af8a29d56f
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStoppingTime_cappedNormExitSequence

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_CadlagExitLocalization_F000
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_b755025803f0c28ce74bcca6

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
theorem _root_.Prove2MeSourceProof.h_6e6c0736914066f88cc333e2
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) (n : ℕ) :
    IsStoppingTime F (cappedNormExitSequence X n) :=
  ((_root_.Prove2MeSourceProof.h_b755025803f0c28ce74bcca6 ha) hF (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hc)
    ((n + 1 : ℕ) : ℝ)).min (isStoppingTime_const F ((n + 1 : ℕ) : ℝ≥0))
end Adapted

end MeasureTheory


