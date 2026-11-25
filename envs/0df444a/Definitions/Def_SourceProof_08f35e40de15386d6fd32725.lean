-- Prove2me | Definitions.Def_SourceProof_08f35e40de15386d6fd32725
-- name    : SourceProof_08f35e40de15386d6fd32725
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:40.396845+00:00
-- url     : https://prove2.me/theorems/779939c5-caff-4415-9c95-17cc380d6980
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.isCagladPath

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_83e2df15639a4620c7f37049
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Topology.Algebra.Monoid
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
theorem _root_.Prove2MeSourceProof.h_08f35e40de15386d6fd32725 {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F)
    (ω : Ω) : IsCagladPath (fun t ↦ H t ω) := by
  rw [← hH.choose_spec]
  exact (_root_.Prove2MeSourceProof.h_83e2df15639a4620c7f37049 hH.choose) ω
end IsSimplePredictable

end ProbabilityTheory


