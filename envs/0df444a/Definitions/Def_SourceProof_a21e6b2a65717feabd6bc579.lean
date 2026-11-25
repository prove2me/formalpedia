-- Prove2me | Definitions.Def_SourceProof_a21e6b2a65717feabd6bc579
-- name    : SourceProof_a21e6b2a65717feabd6bc579
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:24:31.792811+00:00
-- url     : https://prove2.me/theorems/6294f648-6346-5b3a-90ef-ba9ecd9df0e6
-- title:
--   StochLean source theorem: ProbabilityTheory.HasContinuousPaths.stochasticExponentialJumpProduct_eq_one

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticExponential_Basic_F000
import Definitions.Def_SourceProof_3bb9a7fade1f7d012d20523e
import Definitions.Def_SourceProof_911b993558830136570eb23c

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

namespace HasContinuousPaths
omit [IsFiniteMeasure P] in
theorem _root_.Prove2MeSourceProof.h_a21e6b2a65717feabd6bc579
    (hc : HasContinuousPaths X P) : Indistinguishable (stochasticExponentialJumpProduct X) 1 P := by
  filter_upwards [hc] with ω hω t
  have hj (s : Ioc 0 t) : ProbabilityTheory.jumpProcess X s ω = 0 := (_root_.Prove2MeSourceProof.h_3bb9a7fade1f7d012d20523e hω) (ne_of_gt s.2.1)
  simp only [ProbabilityTheory.stochasticExponentialJumpProduct, hj, _root_.Prove2MeSourceProof.h_911b993558830136570eb23c, tprod_one,
    Pi.one_apply]
end HasContinuousPaths

end ProbabilityTheory


