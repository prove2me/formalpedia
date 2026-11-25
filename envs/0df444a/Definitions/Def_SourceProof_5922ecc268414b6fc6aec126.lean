-- Prove2me | Definitions.Def_SourceProof_5922ecc268414b6fc6aec126
-- name    : SourceProof_5922ecc268414b6fc6aec126
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:19:24.345148+00:00
-- url     : https://prove2.me/theorems/729786fb-f1c8-4429-a0d3-54f8acb8c95e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.tendstoUCP_leftRiemannSum_leftLimit_of_cadlag

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_SourceProof_0131e45303b58ff162435f63
import Definitions.Def_SourceProof_0146b8a6534f7d6ff6a61309
import Definitions.Def_SourceProof_12d34a5d964556d97aab2788
import Definitions.Def_SourceProof_2c17b05ac872d393f5e26db2
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
import Definitions.Def_SourceProof_51d9d89e44d55b7a2162d89e
import Definitions.Def_SourceProof_53bca36d7403deaa0689f5ec
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_60fbb0806e5cb393cb74e054
import Definitions.Def_SourceProof_67aa45a3af307cb4d46b1678
import Definitions.Def_SourceProof_83e2df15639a4620c7f37049
import Definitions.Def_SourceProof_9c5e30e37c7ae3d824080fb0
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_aceac4645e3b286f6ad56fcd
import Definitions.Def_SourceProof_cad965745163d481badd0dcb
import Definitions.Def_SourceProof_cd00fe2f60008bc21a9c2833
import Definitions.Def_SourceProof_d2b77a9c3200634f142d37a0
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e
import Definitions.Def_SourceProof_e4bd42219ccf96bf1c27c368
import Definitions.Def_SourceProof_efe23ccbf6a82dd59df5d03e
import Definitions.Def_SourceProof_f60f6796fd78b83be1f764d1
import Definitions.Def_SourceProof_ff07642989734d14cb2ac8eb
import Mathlib.Topology.Algebra.Ring.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Random Riemann approximation for cadlag integrands

Left sampling of a discontinuous path need not converge uniformly to its left
limit. We instead approximate that left limit by source simple processes, take
their right limits, and use partition-uniform continuity of the Riemann sums.
The limit is the source integral of `Y₋`, with its prescribed zero initial value.
There is no restriction on the integrator's initial random variable.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_5922ecc268414b6fc6aec126
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F Y) (hr : HasCadlagPaths Y P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess Y X) atTop
      (hX.stochasticIntegral hF ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 ha) hF hr)
        (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hr)) := by
  let haL := (_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 ha) hF hr
  let hrL := (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hr)
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd haL hF hrL
  choose R hR using hS
  have hS (k : ℕ) : ProbabilityTheory.IsSimplePredictable (S k) F := ⟨R k, hR k⟩
  have huR : ProbabilityTheory.TendstoUCP P (fun k ↦ (R k).toProcess) atTop (ProbabilityTheory.leftLimitProcess Y) := by
    simpa only [hR] using huS
  have hrR (k : ℕ) : ProbabilityTheory.HasCagladPaths (R k).toProcess P :=
    ae_of_all _ (_root_.Prove2MeSourceProof.h_83e2df15639a4620c7f37049 (R k))
  have huRight : ProbabilityTheory.TendstoUCP P (fun k ↦ ProbabilityTheory.rightLimitProcess (R k).toProcess) atTop Y :=
    (_root_.Prove2MeSourceProof.h_9c5e30e37c7ae3d824080fb0 ((_root_.Prove2MeSourceProof.h_e4bd42219ccf96bf1c27c368 huR) hrR hrL))
      (_root_.Prove2MeSourceProof.h_0131e45303b58ff162435f63 hr)
  let C : ℕ → ℝ≥0 → Ω → ℝ := fun k t ω ↦
    (R k).integralProcess X t ω - (R k).initial ω * X 0 ω
  have hC : ProbabilityTheory.TendstoUCP P C atTop (hX.stochasticIntegral hF haL hrL) := by
    have hu := (_root_.Prove2MeSourceProof.h_cad965745163d481badd0dcb ((_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF haL hrL hS huS))
    have heq (k : ℕ) : (hS k).elementaryIntegralProcess X = (R k).integralProcess X :=
      (_root_.Prove2MeSourceProof.h_67aa45a3af307cb4d46b1678 (hS k)) (R k) (hR k) X
    simp only [heq, _root_.Prove2MeSourceProof.h_0146b8a6534f7d6ff6a61309] at hu
    apply (_root_.Prove2MeSourceProof.h_9c5e30e37c7ae3d824080fb0 hu)
    filter_upwards [(_root_.Prove2MeSourceProof.h_d2b77a9c3200634f142d37a0 hX) hF haL hrL] with ω hω t
    simp only [_root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788, Pi.zero_apply, zero_mul] at hω
    simp only [hω, sub_zero]
  apply _root_.Prove2MeSourceProof.h_cd00fe2f60008bc21a9c2833
    (A := fun k n ↦ (π n).leftRiemannSumProcess (ProbabilityTheory.rightLimitProcess (R k).toProcess) X)
    (C := C) _ hC
  · intro n
    have hzero : ProbabilityTheory.TendstoUCP P (fun k ↦ ProbabilityTheory.rightLimitProcess (R k).toProcess - Y) atTop 0 := by
      simpa only [sub_self] using (_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb huRight) (_root_.Prove2MeSourceProof.h_60fbb0806e5cb393cb74e054 atTop Y)
    have hu := (_root_.Prove2MeSourceProof.h_aceac4645e3b286f6ad56fcd hX) hF (fun k ↦ π (n k))
      (fun k ↦ ((_root_.Prove2MeSourceProof.h_f60f6796fd78b83be1f764d1 (_root_.Prove2MeSourceProof.h_51d9d89e44d55b7a2162d89e (R k))) hF (hrR k)).sub ha)
      (fun k ↦ (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 (_root_.Prove2MeSourceProof.h_53bca36d7403deaa0689f5ec (hrR k))) hr))) hzero
    simpa only [_root_.Prove2MeSourceProof.h_efe23ccbf6a82dd59df5d03e] using hu
  · intro k
    exact (_root_.Prove2MeSourceProof.h_2c17b05ac872d393f5e26db2 (R k)) hπ (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)
end IsSemimartingale

end ProbabilityTheory


