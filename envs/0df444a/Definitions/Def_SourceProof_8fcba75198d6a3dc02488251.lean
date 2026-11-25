-- Prove2me | Definitions.Def_SourceProof_8fcba75198d6a3dc02488251
-- name    : SourceProof_8fcba75198d6a3dc02488251
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:45:14.666909+00:00
-- url     : https://prove2.me/theorems/33d2b478-d781-44b6-8f2c-f9daec49f4a7
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasCadlagPaths_stochasticExponentialJumpProduct

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticExponential_Basic_F001
import Definitions.Def_SourceProof_1079144fe60f0ff536db6816
import Definitions.Def_SourceProof_472bb0fb2e5ea3f0d733b6e5
import Definitions.Def_SourceProof_c00d36002cf69560fd2a8d00
import Mathlib.Analysis.Normed.Ring.InfiniteProd

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Cadlag paths of the actual stochastic-exponential product expression

Local square-summability controls all factor deviations. The one-sided
product limits hold on a common event for every finite time, including
after a vanishing or negative factor.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_8fcba75198d6a3dc02488251
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasCadlagPaths (stochasticExponentialJumpProduct X) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_472bb0fb2e5ea3f0d733b6e5 hX) hF] with ω hs
  exact _root_.Prove2MeSourceProof.h_1079144fe60f0ff536db6816 (f := fun s ↦ StochLean.exponentialJumpFactor (ProbabilityTheory.jumpProcess X s ω))
    (fun T ↦ _root_.Prove2MeSourceProof.h_c00d36002cf69560fd2a8d00 (hs T))
end IsSemimartingale

end ProbabilityTheory


