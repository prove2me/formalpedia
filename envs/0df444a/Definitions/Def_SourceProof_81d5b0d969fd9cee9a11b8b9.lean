-- Prove2me | Definitions.Def_SourceProof_81d5b0d969fd9cee9a11b8b9
-- name    : SourceProof_81d5b0d969fd9cee9a11b8b9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:38:25.523337+00:00
-- url     : https://prove2.me/theorems/01e8aa94-71a2-5a78-88de-64108d955bef
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasMonotonePaths_quadraticVariation

import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_36da4c661fc115cbdc2bfff4
import Definitions.Def_SourceProof_6ec6ed103d98506e37900b2a
import Definitions.Def_SourceProof_bdec5e656a0fd313eca02467
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
theorem _root_.Prove2MeSourceProof.h_81d5b0d969fd9cee9a11b8b9
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasMonotonePaths (hX.quadraticVariation hF) P := by
  apply (_root_.Prove2MeSourceProof.h_bdec5e656a0fd313eca02467 hX) hF
    (_root_.Prove2MeSourceProof.h_6ec6ed103d98506e37900b2a
      _root_.Prove2MeSourceProof.h_36da4c661fc115cbdc2bfff4
      (T := fun n ↦ (n : ℝ≥0)) tendsto_natCast_atTop_atTop)
end IsSemimartingale

end ProbabilityTheory


