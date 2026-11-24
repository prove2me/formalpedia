-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
-- name    : StochLean_Probability_Process_Path_RightContinuous_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:15:56.261111+00:00
-- url     : https://prove2.me/theorems/03eb5f27-3a17-486c-8dd1-fa1d79a42d2d
-- title:
--   StochLean: Probability.Process.Path.RightContinuous F000

import Definitions.Def_StochLean_Probability_Process_Path_Monotone_F000
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Almost-sure right-continuous paths
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

section PathDefinitions

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [Preorder T] [TopologicalSpace T] [TopologicalSpace E]

/-- A deterministic path is right-continuous when it is continuous at every time within the
corresponding upper interval. -/
def IsRightContinuousPath (x : T → E) : Prop :=
  ∀ t, ContinuousWithinAt x (Ici t) t
/-- A process has almost-sure right-continuous paths when one common full-measure event supports
right-continuity at every time. -/
def HasRightContinuousPaths (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, IsRightContinuousPath fun t ↦ X t ω
namespace HasRightContinuousPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

end HasRightContinuousPaths

end PathDefinitions

namespace IsModification

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [LinearOrder T] [TopologicalSpace T] [OrderTopology T] [DenselyOrdered T] [NoMaxOrder T]
  [FirstCountableTopology T] [TopologicalSpace.SeparableSpace T] [Nonempty T]
  [TopologicalSpace E] [T2Space E] {X Y : T → Ω → E} {P : Measure Ω}

end IsModification

end ProbabilityTheory


