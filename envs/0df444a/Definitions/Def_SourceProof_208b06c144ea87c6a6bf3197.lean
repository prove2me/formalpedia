-- Prove2me | Definitions.Def_SourceProof_208b06c144ea87c6a6bf3197
-- name    : SourceProof_208b06c144ea87c6a6bf3197
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:37:09.919159+00:00
-- url     : https://prove2.me/theorems/11c20e19-cb0e-5233-8925-93fe852e3d7a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.tendstoUCP_leftRiemannSum_zero_of_stoppingValues

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F000
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_SourceProof_4f97b7466c0eb87e9a60c2a4
import Definitions.Def_SourceProof_683160b98a33817cd725c918
import Definitions.Def_SourceProof_85cd6acbb88cb0e0bb47ef85
import Definitions.Def_SourceProof_88f453bd0ef1e94233e7a1e2
import Definitions.Def_SourceProof_a76267fbd246c80475c88941
import Definitions.Def_SourceProof_cad965745163d481badd0dcb
import Definitions.Def_SourceProof_fb8fd33ada8d5a5f8c30b718
import Mathlib.Topology.Algebra.Group.Basic

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
theorem _root_.Prove2MeSourceProof.h_208b06c144ea87c6a6bf3197
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {Y : ℕ → ℝ≥0 → Ω → ℝ} (π : ℕ → StoppingTimePartition F)
    (h0 : ∀ n, Measurable[F 0] (Y n 0))
    (hcoef : ∀ n (i : Fin (π n).size),
      Measurable[((π n).point i.castSucc).measurableSpace]
        (fun ω ↦ Y n ((π n).point i.castSucc ω) ω))
    (hu : TendstoUCP P Y atTop 0) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess (Y n) X) atTop 0 := by
  let hS n := (_root_.Prove2MeSourceProof.h_4f97b7466c0eb87e9a60c2a4 (π n)) (h0 n) (hcoef n)
  have hJ := (_root_.Prove2MeSourceProof.h_85cd6acbb88cb0e0bb47ef85 hX) hF hS ((_root_.Prove2MeSourceProof.h_a76267fbd246c80475c88941 hu) π)
  have heq (n : ℕ) : (π n).leftRiemannSumProcess (Y n) X =
      fun t ω ↦ (hS n).elementaryIntegralProcess X t ω -
        (hS n).elementaryIntegralProcess X 0 ω := by
    rw [(_root_.Prove2MeSourceProof.h_fb8fd33ada8d5a5f8c30b718 (π n))
      (h0 n) (hcoef n) (hS n) X]
    simp only [_root_.Prove2MeSourceProof.h_683160b98a33817cd725c918,
      _root_.Prove2MeSourceProof.h_88f453bd0ef1e94233e7a1e2]
  convert! (_root_.Prove2MeSourceProof.h_cad965745163d481badd0dcb hJ) using 1 <;> simp only [heq, Pi.zero_apply, sub_self]
  rfl
end IsSemimartingale

end ProbabilityTheory


