-- Prove2me | Definitions.Def_SourceProof_0118c27a775120f687829944
-- name    : SourceProof_0118c27a775120f687829944
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-26T07:29:16.621749+00:00
-- url     : https://prove2.me/theorems/2ced55d7-b978-5b92-9a9d-7f6d6069186e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isComplexSemimartingale_stochasticAreaExponential

import Definitions.Def_SourceProof_2399ce28b0acffae92d96dff
import Definitions.Def_SourceProof_eb7ea992a38d55984d413f3e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The actual Riccati-compensated area exponential

The clock is explicit: it may be deterministic time or the existing continuous
bracket. The process is constructed from the actual area integral, and its
semimartingale, continuity, endpoint and norm properties are proved here.
The local-martingale property still requires the stochastic drift calculation.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_0118c27a775120f687829944
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P) (u T : ℝ) :
    IsComplexSemimartingale (hX.stochasticAreaExponential hY hF Q u T) F P :=
  (_root_.Prove2MeSourceProof.h_2399ce28b0acffae92d96dff ((_root_.Prove2MeSourceProof.h_eb7ea992a38d55984d413f3e hX) hY hQ hF u T))
    hF Complex.differentiable_exp
end IsSemimartingale

end ProbabilityTheory


