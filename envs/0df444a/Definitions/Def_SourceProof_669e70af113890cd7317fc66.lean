-- Prove2me | Definitions.Def_SourceProof_669e70af113890cd7317fc66
-- name    : SourceProof_669e70af113890cd7317fc66
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:00:40.459978+00:00
-- url     : https://prove2.me/theorems/7deaffe2-c7d5-4a4c-80cc-27ea536b174b
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCagladPaths.add

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_2788bc818189572242b6cda6
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

namespace HasCagladPaths
theorem _root_.Prove2MeSourceProof.h_669e70af113890cd7317fc66 [Add E] [ContinuousAdd E]
    (hX : HasCagladPaths X P) (hY : HasCagladPaths Y P) : HasCagladPaths (X + Y) P := by
  filter_upwards [hX, hY] with ω hx hy
  exact (_root_.Prove2MeSourceProof.h_2788bc818189572242b6cda6 hx) hy
end HasCagladPaths

variable [OrderBot T]

end ProbabilityTheory


