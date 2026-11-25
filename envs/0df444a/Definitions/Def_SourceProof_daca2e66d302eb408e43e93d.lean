-- Prove2me | Definitions.Def_SourceProof_daca2e66d302eb408e43e93d
-- name    : SourceProof_daca2e66d302eb408e43e93d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:46:51.547149+00:00
-- url     : https://prove2.me/theorems/a4547caa-c6a5-48c3-8010-36cb9ced56e0
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasFiniteVariationPaths_stochasticExponentialJumpProduct

import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticExponential_Basic_F000
import Definitions.Def_SourceProof_472bb0fb2e5ea3f0d733b6e5
import Definitions.Def_SourceProof_c00d36002cf69560fd2a8d00
import Definitions.Def_SourceProof_d74afafd51c92049941a84c1
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite variation of the actual stochastic-exponential jump product

This is a pathwise conclusion on one full-measure event for every horizon.
No expected-variation bound, nonvanishing hypothesis, or adaptedness of
an uncountably indexed product is silently assumed.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_daca2e66d302eb408e43e93d
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasFiniteVariationPaths (stochasticExponentialJumpProduct X) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_472bb0fb2e5ea3f0d733b6e5 hX) hF] with ω hs
  exact _root_.Prove2MeSourceProof.h_d74afafd51c92049941a84c1
    (f := fun s ↦ StochLean.exponentialJumpFactor (ProbabilityTheory.jumpProcess X s ω))
    (fun T ↦ _root_.Prove2MeSourceProof.h_c00d36002cf69560fd2a8d00 (hs T))
end IsSemimartingale

end ProbabilityTheory


