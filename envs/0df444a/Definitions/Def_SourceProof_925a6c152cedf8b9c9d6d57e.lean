-- Prove2me | Definitions.Def_SourceProof_925a6c152cedf8b9c9d6d57e
-- name    : SourceProof_925a6c152cedf8b9c9d6d57e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:50:07.289798+00:00
-- url     : https://prove2.me/theorems/8dc7211c-3d7c-4ec8-a8fc-ce86b5736df5
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticCovariation_eq_product_sub_integrals

import Definitions.Def_StochLean_Probability_Process_Partition_CrossSums_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_F000
import Definitions.Def_SourceProof_215f6d5e6b10999a8c8f10ba
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_5922ecc268414b6fc6aec126
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_6443755938a3801e72d73393
import Definitions.Def_SourceProof_992997dcec9963390c8c98e7
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
import Definitions.Def_SourceProof_eb79ab10a8ab282316156b75
import Definitions.Def_SourceProof_ff07642989734d14cb2ac8eb
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Integration by parts and the algebra of semimartingales

The identity is deduced from actual random-partition mixed sums and the
cadlag-integrand Riemann theorem. It identifies the existing polarized bracket;
the product formula is not used as a competing definition of covariation.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_925a6c152cedf8b9c9d6d57e
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (X * Y - hY.stochasticIntegral hF
        ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
        (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) -
      hX.stochasticIntegral hF
        ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY))
        (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY))) P := by
  apply (_root_.Prove2MeSourceProof.h_6443755938a3801e72d73393 hX) hY hF
  · intro π hπ
    have hprod := (_root_.Prove2MeSourceProof.h_215f6d5e6b10999a8c8f10ba hπ) (X * Y)
    have hu := (_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb ((_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb hprod) ((_root_.Prove2MeSourceProof.h_5922ecc268414b6fc6aec126 hY)
      hF (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX) hπ)))
        ((_root_.Prove2MeSourceProof.h_5922ecc268414b6fc6aec126 hX) hF (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY) hπ)
    have heq (n : ℕ) :
        (fun t ω ↦ (X * Y) (min ((π n).terminal ω) t) ω) -
          (π n).leftRiemannSumProcess X Y - (π n).leftRiemannSumProcess Y X =
        (π n).quadraticCovariationSumProcess X Y := by
      funext t ω
      exact ((_root_.Prove2MeSourceProof.h_eb79ab10a8ab282316156b75 (π n)) X Y t ω).symm
    rw [show (fun n ↦ (fun t ω ↦ (X * Y) (min ((π n).terminal ω) t) ω) -
      (π n).leftRiemannSumProcess X Y - (π n).leftRiemannSumProcess Y X) =
        (fun n ↦ (π n).quadraticCovariationSumProcess X Y) from funext heq] at hu
    exact hu
  · exact (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_992997dcec9963390c8c98e7 (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY)))
      ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hY) hF
        ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
        (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)))))
      ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF
        ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY))
        (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY)))))
end IsSemimartingale

end ProbabilityTheory


