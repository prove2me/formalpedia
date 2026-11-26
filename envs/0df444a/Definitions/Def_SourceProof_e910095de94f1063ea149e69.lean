-- Prove2me | Definitions.Def_SourceProof_e910095de94f1063ea149e69
-- name    : SourceProof_e910095de94f1063ea149e69
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-26T07:28:53.829127+00:00
-- url     : https://prove2.me/theorems/404224d3-5666-5e28-80e6-df2da9d86f1b
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isComplexSemimartingale_characteristicExponential

import Definitions.Def_SourceProof_2399ce28b0acffae92d96dff
import Definitions.Def_SourceProof_44e1865b649fa0c29b61b82f

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
theorem _root_.Prove2MeSourceProof.h_e910095de94f1063ea149e69
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (u : ℝ) :
    IsComplexSemimartingale (hX.characteristicExponential hF u) F P :=
  (_root_.Prove2MeSourceProof.h_2399ce28b0acffae92d96dff ((_root_.Prove2MeSourceProof.h_44e1865b649fa0c29b61b82f hX) hF u))
    hF Complex.differentiable_exp
end IsSemimartingale

end ProbabilityTheory


