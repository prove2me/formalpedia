-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticExponential_Basic_F000
-- name    : StochLean_Probability_Process_Semimartingale_StochasticExponential_Basic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:17:44.540413+00:00
-- url     : https://prove2.me/theorems/fdb9eba4-7fe3-42f3-8a12-58bc5a401ae9
-- title:
--   StochLean: Probability.Process.Semimartingale.StochasticExponential.Basic F000

import Definitions.Def_StochLean_Analysis_PathVariation_ExponentialJumpFactor_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000

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

noncomputable def stochasticExponentialJumpProduct {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∏' s : Ioc 0 t, exponentialJumpFactor (jumpProcess X s ω)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

end ProbabilityTheory


