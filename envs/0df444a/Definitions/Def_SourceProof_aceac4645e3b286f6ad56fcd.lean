-- Prove2me | Definitions.Def_SourceProof_aceac4645e3b286f6ad56fcd
-- name    : SourceProof_aceac4645e3b286f6ad56fcd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:42:36.376609+00:00
-- url     : https://prove2.me/theorems/ebc4c4a5-7f67-5825-be0f-18013e9c2bf8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.tendstoUCP_leftRiemannSum_zero_of_rightContinuous

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_208b06c144ea87c6a6bf3197
import Definitions.Def_SourceProof_4aad6e35fadea08fff8ce9d0
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Partition-uniform UCP continuity of increment-only Riemann sums

The partitions may vary arbitrarily with the input index. Source UCP continuity
and the compact-deviation contraction give uniformity without a mesh condition.
The initial product is removed by stopping the same source integral at zero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_aceac4645e3b286f6ad56fcd
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {Y : ℕ → ℝ≥0 → Ω → ℝ} (π : ℕ → StoppingTimePartition F)
    (ha : ∀ n, Adapted F (Y n)) (hr : ∀ n, HasRightContinuousPaths (Y n) P)
    (hu : TendstoUCP P Y atTop 0) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess (Y n) X) atTop 0 :=
  (_root_.Prove2MeSourceProof.h_208b06c144ea87c6a6bf3197 hX) hF π (fun n ↦ ha n 0)
    (fun n i ↦ (_root_.Prove2MeSourceProof.h_4aad6e35fadea08fff8ce9d0 (ha n).stronglyAdapted) hF (hr n)
      ((π n).point i.castSucc).isStoppingTime) hu
end IsSemimartingale

end ProbabilityTheory


