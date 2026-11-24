-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
-- name    : StochLean_Probability_Process_Path_Cadlag_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:56:48.243981+00:00
-- url     : https://prove2.me/theorems/e8db730c-3a06-4645-822c-4111bea1a106
-- title:
--   StochLean: Probability.Process.Path.Cadlag F001

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

namespace HasLeftContinuousPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

end HasLeftContinuousPaths

namespace IsContinuousPath

end IsContinuousPath

end LeftContinuous

section Cadlag

variable [LinearOrder T] [TopologicalSpace T] [OrderBot T]
  [TopologicalSpace E]

/-- A deterministic càdlàg path is right-continuous and has a finite strict-left limit at every
time other than the lower endpoint. The existential limit keeps the predicate on its natural
domain and does not use a totalized `leftLim` fallback value. -/
def IsCadlagPath (x : T → E) : Prop :=
  IsRightContinuousPath x ∧
    ∀ t, t ≠ ⊥ → ∃ y : E, Tendsto x (nhdsWithin t (Iio t)) (𝓝 y)
/-- A process has càdlàg paths when one common full-measure event supports the whole trajectory
property. -/
def HasCadlagPaths (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, IsCadlagPath fun t ↦ X t ω
namespace HasCadlagPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

end HasCadlagPaths

end Cadlag

end ProbabilityTheory


