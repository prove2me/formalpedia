-- Prove2me | Definitions.Def_SourceProof_6443755938a3801e72d73393
-- name    : SourceProof_6443755938a3801e72d73393
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:41:57.64454+00:00
-- url     : https://prove2.me/theorems/793b1d73-8bd1-43cb-a877-1d224856a94d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticCovariation_indistinguishable_of_limits

import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F001
import Definitions.Def_StochLean_Probability_Process_Partition_CrossSums_F000
import Definitions.Def_SourceProof_0f6a1de2f7189d335c4ff9a7
import Definitions.Def_SourceProof_36da4c661fc115cbdc2bfff4
import Definitions.Def_SourceProof_6ec6ed103d98506e37900b2a
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_ae584a9168b1bd16f954b4f8
import Definitions.Def_SourceProof_d131488cf582eb29dc48ae9b

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Mixed increment sums converge to the polarized raw covariation

The characterization below uses genuine partition limits, not an assumed
bilinearity of the square bracket or continuity in the integrator.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_6443755938a3801e72d73393
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hZ : ∀ (π : ℕ → StoppingTimePartition F),
      StoppingTimePartition.IsTendingToIdentity π P →
      TendstoUCP P (fun n ↦ (π n).quadraticCovariationSumProcess X Y) atTop Z)
    (hrZ : HasRightContinuousPaths Z P) :
    Indistinguishable (hX.quadraticCovariation hY hF) Z P := by
  let π : ℕ → ProbabilityTheory.StoppingTimePartition F := fun n ↦ ProbabilityTheory.StoppingTimePartition.deterministic F
    ((StochLean.LocallyFinitePartition.dyadic n).restrict n)
  have hπ : ProbabilityTheory.StoppingTimePartition.IsTendingToIdentity π P :=
    _root_.Prove2MeSourceProof.h_6ec6ed103d98506e37900b2a
      _root_.Prove2MeSourceProof.h_36da4c661fc115cbdc2bfff4 tendsto_natCast_atTop_atTop
  exact (_root_.Prove2MeSourceProof.h_ae584a9168b1bd16f954b4f8 ((_root_.Prove2MeSourceProof.h_d131488cf582eb29dc48ae9b hX) hY hF hπ))
    (hZ π hπ) (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_0f6a1de2f7189d335c4ff9a7 hX) hY hF)) hrZ
end IsSemimartingale

end ProbabilityTheory


