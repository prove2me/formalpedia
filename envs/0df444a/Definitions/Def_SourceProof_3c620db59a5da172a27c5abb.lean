-- Prove2me | Definitions.Def_SourceProof_3c620db59a5da172a27c5abb
-- name    : SourceProof_3c620db59a5da172a27c5abb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:22:30.252864+00:00
-- url     : https://prove2.me/theorems/ada84457-dfaa-41b2-b5be-98a044c13bbe
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.tendstoUCP_weightedQuadraticCovariationSum

import Definitions.Def_StochLean_Probability_Process_Partition_WeightedCrossSums_F000
import Definitions.Def_SourceProof_12d004eabf16e25ed057471d
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_328fe50a92ac939773c20a20
import Definitions.Def_SourceProof_523d7cde826eec51d63a0e17
import Definitions.Def_SourceProof_5922ecc268414b6fc6aec126
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_79b70fbdac96840530cd88fc
import Definitions.Def_SourceProof_992997dcec9963390c8c98e7
import Definitions.Def_SourceProof_9a15eada3555a513322a1de0
import Definitions.Def_SourceProof_9c5e30e37c7ae3d824080fb0
import Definitions.Def_SourceProof_ba54eeb3a2661e253611936f
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
import Definitions.Def_SourceProof_f10c0f6fee878e1d0d16f7ba
import Definitions.Def_SourceProof_ff07642989734d14cb2ac8eb

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Protter II.30: weighted random-partition mixed sums

For an adapted cadlag weight H, actual weighted increment sums converge in
UCP to the constructed integral of H₋ against the unique raw mixed bracket.
The source H₀₋ is zero. No boundedness, moment, continuity or deterministic
partition assumption is added. The proof uses II.21 and associativity, not
an invalid uniform approximation of a discontinuous sampled integrand.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_3c620db59a5da172a27c5abb
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCadlagPaths H P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).weightedQuadraticCovariationSumProcess H X Y) atTop
      (((_root_.Prove2MeSourceProof.h_9a15eada3555a513322a1de0 hX) hY hF).stochasticIntegral hF
        ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 ha) hF hr) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hr)) := by
  let haHL := (_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 ha) hF hr
  let hrHL := (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hr)
  let haHX : Adapted F (H * X) := fun t ↦ (ha t).mul ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) t)
  let haHY : Adapted F (H * Y) := fun t ↦ (ha t).mul ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY) t)
  let hrHX := (_root_.Prove2MeSourceProof.h_992997dcec9963390c8c98e7 hr) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)
  let hrHY := (_root_.Prove2MeSourceProof.h_992997dcec9963390c8c98e7 hr) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY)
  have hu := (_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb ((_root_.Prove2MeSourceProof.h_5922ecc268414b6fc6aec126 ((_root_.Prove2MeSourceProof.h_ba54eeb3a2661e253611936f hX) hY hF)) hF ha hr hπ))
    ((_root_.Prove2MeSourceProof.h_5922ecc268414b6fc6aec126 hY) hF haHX hrHX hπ)
  have hu' := (_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb hu) ((_root_.Prove2MeSourceProof.h_5922ecc268414b6fc6aec126 hX) hF haHY hrHY hπ)
  have hbridge := (_root_.Prove2MeSourceProof.h_12d004eabf16e25ed057471d hX) hY hF haHL hrHL
  have hYeq := (_root_.Prove2MeSourceProof.h_79b70fbdac96840530cd88fc hY) hF
    ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 haHX) hF hrHX) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hrHX)
    (fun t ↦ (haHL t).mul
      ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX) t))
    ((_root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 hrHL) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)))
    ((_root_.Prove2MeSourceProof.h_328fe50a92ac939773c20a20 hr) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
  have hXeq := (_root_.Prove2MeSourceProof.h_79b70fbdac96840530cd88fc hX) hF
    ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 haHY) hF hrHY) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hrHY)
    (fun t ↦ (haHL t).mul
      ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY) t))
    ((_root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 hrHL) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY)))
    ((_root_.Prove2MeSourceProof.h_328fe50a92ac939773c20a20 hr) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY))
  have htarget : ProbabilityTheory.Indistinguishable
      (((_root_.Prove2MeSourceProof.h_ba54eeb3a2661e253611936f hX) hY hF).stochasticIntegral hF haHL hrHL -
        hY.stochasticIntegral hF ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 haHX) hF hrHX)
          (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hrHX) -
        hX.stochasticIntegral hF ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 haHY) hF hrHY)
          (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hrHY))
      (((_root_.Prove2MeSourceProof.h_9a15eada3555a513322a1de0 hX) hY hF).stochasticIntegral hF haHL hrHL) P := by
    filter_upwards [hbridge, hYeq, hXeq] with ω hb hy hx t
    simp only [Pi.sub_apply, hb t, hy t, hx t]
  simpa only [_root_.Prove2MeSourceProof.h_f10c0f6fee878e1d0d16f7ba]
    using (_root_.Prove2MeSourceProof.h_9c5e30e37c7ae3d824080fb0 hu') htarget
end IsSemimartingale

end ProbabilityTheory


