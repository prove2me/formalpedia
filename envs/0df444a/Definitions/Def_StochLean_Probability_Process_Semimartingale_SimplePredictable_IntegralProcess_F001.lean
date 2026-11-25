-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:50:26.027813+00:00
-- url     : https://prove2.me/theorems/560fb765-0f0c-438f-9769-afaaab83d5b3
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.IntegralProcess F001

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

end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

/-- Protter's source `J_X(H)`, before any extension beyond simple predictable integrands. -/
noncomputable def elementaryIntegralProcess (hH : IsSimplePredictable H F)
    (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ↦ hH.elementaryIntegral (fun s ω ↦ X (min s t) ω)
end IsSimplePredictable
end ProbabilityTheory


