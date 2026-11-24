-- Prove2me | Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
-- name    : SourceProof_7e41a7708f0759111a0ce622
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:14:37.243335+00:00
-- url     : https://prove2.me/theorems/26b91665-b205-4b23-8ce0-aeabebcf74df
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.indicator

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_a2cb63993a652b5632791121
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
theorem _root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 [Zero E] (hX : HasCadlagPaths X P) (s : Set Ω) :
    HasCadlagPaths (fun t ↦ s.indicator (X t)) P := by
  filter_upwards [hX] with ω hω
  by_cases h : ω ∈ s
  · simpa only [Set.indicator_of_mem h] using hω
  · simp only [Set.indicator_of_notMem h]
    exact _root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121 continuous_const
end HasCadlagPaths

end ProbabilityTheory


