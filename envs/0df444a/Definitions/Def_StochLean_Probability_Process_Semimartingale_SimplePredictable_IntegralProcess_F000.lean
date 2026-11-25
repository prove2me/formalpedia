-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:27.556001+00:00
-- url     : https://prove2.me/theorems/7291b4e7-8c69-4b8f-96e4-560b0ea7dc98
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.IntegralProcess F000

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F002
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The source elementary integral process

Protter's `J_X(H)` is the existing elementary integral evaluated against `X` stopped
at the current deterministic time. This is not another general stochastic integral.
The source initial term is retained, including at time zero.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

/-- Representation-level source integral process, using only the existing finite-sum integral. -/
def integralProcess (H : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ↦ H.integral (fun s ω ↦ X (min s t) ω)
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


