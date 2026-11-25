-- Prove2me | Definitions.Def_SourceProof_0fef2f232d2bf1adcaa99445
-- name    : SourceProof_0fef2f232d2bf1adcaa99445
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:16:45.78472+00:00
-- url     : https://prove2.me/theorems/ee96e020-64ff-47ac-9542-9cf83ce3e0d4
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_congr_integrator

import Definitions.Def_StochLean_Probability_Process_Equivalence_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_5caa95db89fdd596c2cde105
import Definitions.Def_SourceProof_67aa45a3af307cb4d46b1678

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Source integral invariance under indistinguishable integrators -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_0fef2f232d2bf1adcaa99445
    (hH : IsSimplePredictable H F) (hXY : Indistinguishable X Y P) :
    Indistinguishable (hH.elementaryIntegralProcess X) (hH.elementaryIntegralProcess Y) P := by
  rw [(_root_.Prove2MeSourceProof.h_67aa45a3af307cb4d46b1678 hH) hH.choose hH.choose_spec X,
    (_root_.Prove2MeSourceProof.h_67aa45a3af307cb4d46b1678 hH) hH.choose hH.choose_spec Y]
  filter_upwards [hXY] with ω hω t
  simp only [_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105, hω]
end IsSimplePredictable

end ProbabilityTheory


