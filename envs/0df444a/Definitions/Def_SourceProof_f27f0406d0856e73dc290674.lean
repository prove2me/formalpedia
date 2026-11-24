-- Prove2me | Definitions.Def_SourceProof_f27f0406d0856e73dc290674
-- name    : SourceProof_f27f0406d0856e73dc290674
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:00:29.43094+00:00
-- url     : https://prove2.me/theorems/1c676e23-860c-4423-af79-fe5718491197
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.add

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_d80df7975aaa241a180afe6d
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous operations on cadlag and caglad paths

The process statements intersect finitely many common full-measure events.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {T Ω E G : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] [TopologicalSpace G] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X Y : T → Ω → E}

variable [OrderBot T]

namespace HasCadlagPaths
theorem _root_.Prove2MeSourceProof.h_f27f0406d0856e73dc290674 [Add E] [ContinuousAdd E]
    (hX : HasCadlagPaths X P) (hY : HasCadlagPaths Y P) : HasCadlagPaths (X + Y) P := by
  filter_upwards [hX, hY] with ω hx hy
  exact (_root_.Prove2MeSourceProof.h_d80df7975aaa241a180afe6d hx) hy
end HasCadlagPaths

end ProbabilityTheory


