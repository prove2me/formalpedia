-- Prove2me | Definitions.Def_SourceProof_7ca5a4a340ad9cc180bba716
-- name    : SourceProof_7ca5a4a340ad9cc180bba716
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:36:37.172298+00:00
-- url     : https://prove2.me/theorems/bd177103-5750-425f-8093-15f5b84ed592
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.hasCagladPaths

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_08f35e40de15386d6fd32725
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
theorem _root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F)
    (P : Measure Ω) : HasCagladPaths H P := ae_of_all _ (_root_.Prove2MeSourceProof.h_08f35e40de15386d6fd32725 hH)
end IsSimplePredictable

end ProbabilityTheory


