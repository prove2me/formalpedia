-- Prove2me | Definitions.Def_SourceProof_d708bd4cbd825857e79d3668
-- name    : SourceProof_d708bd4cbd825857e79d3668
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:10.458151+00:00
-- url     : https://prove2.me/theorems/51d06bc9-9aa7-4659-91e3-7c4cec40e9e2
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPreLocalizingSequence.tendsto_measure_le

import Definitions.Def_SourceProof_336029c999d97a8ccdc620fb
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Vanishing probabilities of early localization

AE divergence of a pre-localizing sequence already suffices. Monotonicity is not needed
for the probability estimate.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {τ : ℕ → Ω → WithTop ℝ≥0}

namespace IsPreLocalizingSequence
theorem _root_.Prove2MeSourceProof.h_d708bd4cbd825857e79d3668 (hτ : IsPreLocalizingSequence F τ P)
    (T : ℝ≥0) : Tendsto (fun n ↦ P {ω | τ n ω ≤ T}) atTop (𝓝 0) :=
  _root_.Prove2MeSourceProof.h_336029c999d97a8ccdc620fb
    (fun n ↦ (hτ.isStoppingTime n).measurable.mono (hτ.isStoppingTime n).measurableSpace_le le_rfl)
    hτ.tendsto_top T
end IsPreLocalizingSequence

end ProbabilityTheory


