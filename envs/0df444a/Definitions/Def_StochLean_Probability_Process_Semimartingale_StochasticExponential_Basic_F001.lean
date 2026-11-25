-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticExponential_Basic_F001
-- name    : StochLean_Probability_Process_Semimartingale_StochasticExponential_Basic_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:24:18.920743+00:00
-- url     : https://prove2.me/theorems/8459af80-1bf9-589d-a416-803ba373be49
-- title:
--   StochLean: Probability.Process.Semimartingale.StochasticExponential.Basic F001

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticExponential_Basic_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The actual product expression for the stochastic exponential

The expression uses the existing canonical continuous bracket. Its initial
value is exp(X(0)); the source unit-initial equation will require X(0) = 0.
Product convergence is proved here. Semimartingale regularity and the
defining stochastic equation are separate obligations, not assumed fields.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.stochasticExponential
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) : ℝ≥0 → Ω → ℝ := fun t ω ↦
  Real.exp (X t ω - (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF t ω) *
    stochasticExponentialJumpProduct X t ω
end ProbabilityTheory


