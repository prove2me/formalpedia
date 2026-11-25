-- Prove2me | Definitions.Def_SourceProof_feca862e0bd15cee9b184fdf
-- name    : SourceProof_feca862e0bd15cee9b184fdf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:51.5348+00:00
-- url     : https://prove2.me/theorems/b7f1ee9a-4854-4593-855a-fecf7755d977
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCagladPaths.hasLeftContinuousPaths

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Common-event càglàd paths

Chapter II integrands have left-continuous paths with finite right limits.
The existential right limit does not select a default outside this domain.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {T Ω E : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

namespace HasCagladPaths
theorem _root_.Prove2MeSourceProof.h_feca862e0bd15cee9b184fdf {X : T → Ω → E}
    (hX : HasCagladPaths X P) : HasLeftContinuousPaths X P := hX.mono fun _ ↦ And.left
end HasCagladPaths

end ProbabilityTheory


