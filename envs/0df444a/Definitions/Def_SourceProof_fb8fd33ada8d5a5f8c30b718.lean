-- Prove2me | Definitions.Def_SourceProof_fb8fd33ada8d5a5f8c30b718
-- name    : SourceProof_fb8fd33ada8d5a5f8c30b718
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:02:41.568797+00:00
-- url     : https://prove2.me/theorems/f0e07fba-04a8-4265-818b-58dc4629cf69
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.leftRiemannSumProcess_eq_elementaryIntegralProcess_sub_initial

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F000
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F001
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_SourceProof_67aa45a3af307cb4d46b1678
import Definitions.Def_SourceProof_824b0e2c6cd9530a7cfac3d4
import Definitions.Def_SourceProof_c016c088ffde04a6620148ac
import Mathlib.Topology.Algebra.Group.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adaptedness and cadlag paths of increment-only random Riemann sums

These properties follow from the existing source representation and its
independent initial term. The integrator need not be a semimartingale.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {Y X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_fb8fd33ada8d5a5f8c30b718
    (π : StoppingTimePartition F) (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω))
    (hS : IsSimplePredictable (π.leftSampleProcess Y) F) (X : ℝ≥0 → Ω → ℝ) :
    π.leftRiemannSumProcess Y X = fun t ω ↦ hS.elementaryIntegralProcess X t ω - Y 0 ω * X 0 ω := by
  rw [(_root_.Prove2MeSourceProof.h_67aa45a3af307cb4d46b1678 hS) _ ((_root_.Prove2MeSourceProof.h_c016c088ffde04a6620148ac π) Y h0 hcoef) X]
  exact (_root_.Prove2MeSourceProof.h_824b0e2c6cd9530a7cfac3d4 π) Y X h0 hcoef
end ProbabilityTheory.StoppingTimePartition


