-- Prove2me | Definitions.Def_SourceProof_7c758b3f54acb965f59f9d0b
-- name    : SourceProof_7c758b3f54acb965f59f9d0b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:32.56333+00:00
-- url     : https://prove2.me/theorems/11c37137-fce8-4409-98cd-a89736e1d3a7
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCagladPaths.sub

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_923c456011a9fa9af1f50ea3
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Subtraction of cadlag and caglad paths -/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] [Sub E] [ContinuousSub E] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X Y : T → Ω → E}

namespace HasCagladPaths
theorem _root_.Prove2MeSourceProof.h_7c758b3f54acb965f59f9d0b (hX : HasCagladPaths X P) (hY : HasCagladPaths Y P) :
    HasCagladPaths (X - Y) P := by
  filter_upwards [hX, hY] with ω hx hy
  exact (_root_.Prove2MeSourceProof.h_923c456011a9fa9af1f50ea3 hx) hy
end HasCagladPaths

end ProbabilityTheory


