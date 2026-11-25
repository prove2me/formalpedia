-- Prove2me | Definitions.Def_SourceProof_237ca6993b1d0487e6b85da5
-- name    : SourceProof_237ca6993b1d0487e6b85da5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:43:31.86308+00:00
-- url     : https://prove2.me/theorems/807f6858-d573-50b4-9f88-c037c080dfc2
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasFiniteVariationPaths_quadraticVariation

import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_6ed3c177b9234dc2ab8ed747
import Definitions.Def_SourceProof_81d5b0d969fd9cee9a11b8b9
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.UniformSpace.UniformApproximation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Increasing paths of the canonical raw quadratic variation

The partial-cell square sums are not assumed monotone. Evaluating each sum
at the next partition endpoint produces monotone completed-cell sums. A
locally uniform subsequence and right continuity identify their pointwise
limit with the raw bracket on one event for all times together.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_237ca6993b1d0487e6b85da5
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasFiniteVariationPaths (hX.quadraticVariation hF) P :=
  (_root_.Prove2MeSourceProof.h_6ed3c177b9234dc2ab8ed747 ((_root_.Prove2MeSourceProof.h_81d5b0d969fd9cee9a11b8b9 hX) hF))
end IsSemimartingale

end ProbabilityTheory


