-- Prove2me | Definitions.Def_SourceProof_44e1865b649fa0c29b61b82f
-- name    : SourceProof_44e1865b649fa0c29b61b82f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:31:03.789121+00:00
-- url     : https://prove2.me/theorems/97924480-9e23-4360-a078-1b4a38e998b8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isComplexSemimartingale_characteristicExponent

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticExponential_Characteristic_F000
import Definitions.Def_SourceProof_314794411901083e0cc253d3
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_cec55a75e8011931c820c0c2

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The compensated characteristic exponential

The real compensation is positive: its imaginary coefficient has negative
bilinear quadratic variation. This is a function of the existing continuous
real bracket, not a second stochastic integration or bracket construction.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_44e1865b649fa0c29b61b82f
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (u : ℝ) :
    IsComplexSemimartingale (hX.characteristicExponent hF u) F P :=
  (_root_.Prove2MeSourceProof.h_cec55a75e8011931c820c0c2 ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 ((_root_.Prove2MeSourceProof.h_314794411901083e0cc253d3 hX) hF)) ((1 / 2) * u ^ 2)))
    ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) u)
end IsSemimartingale

end ProbabilityTheory


