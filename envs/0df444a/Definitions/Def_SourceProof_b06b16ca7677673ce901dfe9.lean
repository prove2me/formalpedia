-- Prove2me | Definitions.Def_SourceProof_b06b16ca7677673ce901dfe9
-- name    : SourceProof_b06b16ca7677673ce901dfe9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:49.541892+00:00
-- url     : https://prove2.me/theorems/837f767a-7f83-419a-a2ea-4313bdff45aa
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCagladPaths.congr

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
theorem _root_.Prove2MeSourceProof.h_b06b16ca7677673ce901dfe9 {X Y : T → Ω → E}
    (hXY : Indistinguishable X Y P) (hX : HasCagladPaths X P) : HasCagladPaths Y P := by
  filter_upwards [hXY, hX] with ω hω hreg
  have heq : (fun t ↦ X t ω) = fun t ↦ Y t ω := funext hω
  rwa [← heq]
end HasCagladPaths

end ProbabilityTheory


