-- Prove2me | Definitions.Def_SourceProof_d0ba14a65d084d5914c41424
-- name    : SourceProof_d0ba14a65d084d5914c41424
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:21.351624+00:00
-- url     : https://prove2.me/theorems/26c440b6-0b31-4c5d-8b64-1bfaab0cb8d8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.adapted

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_51d9d89e44d55b7a2162d89e
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.Predictable
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Source simple predictable processes really are adapted, caglad and predictable

Coefficient measurability is used at the original left stopping endpoint. Neither
bounded coefficients nor strict separation of endpoints is assumed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) :
    Adapted F H := by
  rw [← hH.choose_spec]
  exact (_root_.Prove2MeSourceProof.h_51d9d89e44d55b7a2162d89e hH.choose)
end IsSimplePredictable

end ProbabilityTheory


