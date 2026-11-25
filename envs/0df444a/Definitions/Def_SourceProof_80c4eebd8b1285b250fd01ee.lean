-- Prove2me | Definitions.Def_SourceProof_80c4eebd8b1285b250fd01ee
-- name    : SourceProof_80c4eebd8b1285b250fd01ee
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:32:49.461799+00:00
-- url     : https://prove2.me/theorems/751bfd2a-456a-4c88-9b7c-4dabcc09de03
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticExponential_of_continuous

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticExponential_Basic_F001
import Definitions.Def_SourceProof_a21e6b2a65717feabd6bc579

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

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_80c4eebd8b1285b250fd01ee
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    Indistinguishable (hX.stochasticExponential hF)
      (fun t ω ↦ Real.exp (X t ω - (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF t ω)) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_a21e6b2a65717feabd6bc579 hc)] with ω hω t
  simp only [ProbabilityTheory.IsSemimartingale.stochasticExponential, hω t, Pi.one_apply, mul_one]
end IsSemimartingale

end ProbabilityTheory


