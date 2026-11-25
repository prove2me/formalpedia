-- Prove2me | Definitions.Def_SourceProof_c2cc59834fa00d679453bf21
-- name    : SourceProof_c2cc59834fa00d679453bf21
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:35:34.706001+00:00
-- url     : https://prove2.me/theorems/aac358cc-8584-59e5-918d-546e994bd7ff
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.ae_tendsto_cappedNormExitSequence

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_CadlagExitLocalization_F000
import Definitions.Def_SourceProof_67a17ea4a85e2e7989d44683

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

namespace HasCadlagPaths
theorem _root_.Prove2MeSourceProof.h_c2cc59834fa00d679453bf21 (hX : HasCadlagPaths X P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ cappedNormExitSequence X n ω) atTop (𝓝 ⊤) :=
  hX.mono fun _ hω ↦ (_root_.Prove2MeSourceProof.h_67a17ea4a85e2e7989d44683 hω)
end HasCadlagPaths

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


