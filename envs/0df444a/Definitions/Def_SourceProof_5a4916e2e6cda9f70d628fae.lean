-- Prove2me | Definitions.Def_SourceProof_5a4916e2e6cda9f70d628fae
-- name    : SourceProof_5a4916e2e6cda9f70d628fae
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:49.089801+00:00
-- url     : https://prove2.me/theorems/806abed9-104d-42e1-b451-832234c5a63f
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.congr

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Almost-sure left-continuous and càdlàg paths

This file provides only trajectory predicates. It does not construct the Skorokhod topology.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}

section LeftContinuous

variable [Preorder T] [TopologicalSpace T] [TopologicalSpace E]

namespace HasLeftContinuousPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

end HasLeftContinuousPaths

namespace IsContinuousPath

end IsContinuousPath

end LeftContinuous

section Cadlag

variable [LinearOrder T] [TopologicalSpace T] [OrderBot T]
  [TopologicalSpace E]

namespace HasCadlagPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_5a4916e2e6cda9f70d628fae (hXY : Indistinguishable X Y P) (hX : HasCadlagPaths X P) :
    HasCadlagPaths Y P := by
  filter_upwards [hXY, hX] with ω hω hcad
  refine ⟨?_, ?_⟩
  · simpa only [ProbabilityTheory.IsRightContinuousPath, hω] using hcad.1
  · intro t ht
    obtain ⟨y, hy⟩ := hcad.2 t ht
    exact ⟨y, hy.congr' (Eventually.of_forall fun u ↦ hω u)⟩
end HasCadlagPaths

end Cadlag

end ProbabilityTheory


