-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
-- name    : StochLean_Probability_Process_Path_Cadlag_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:56:57.734782+00:00
-- url     : https://prove2.me/theorems/e04da036-f7df-40d2-8f2d-967109f85d18
-- title:
--   StochLean: Probability.Process.Path.Cadlag F000

import Definitions.Def_StochLean_Probability_Process_Path_Continuous_F000

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

def IsLeftContinuousPath (x : T → E) : Prop :=
  ∀ t, ContinuousWithinAt x (Iic t) t
def HasLeftContinuousPaths (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, IsLeftContinuousPath fun t ↦ X t ω
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

end HasCadlagPaths

end Cadlag

end ProbabilityTheory


