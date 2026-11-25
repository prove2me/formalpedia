-- Prove2me | Definitions.Def_SourceProof_d131488cf582eb29dc48ae9b
-- name    : SourceProof_d131488cf582eb29dc48ae9b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:32:15.024606+00:00
-- url     : https://prove2.me/theorems/4ce29ba6-16e0-491f-9144-b16232f0519b
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.tendstoUCP_quadraticCovariationSumProcess

import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F001
import Definitions.Def_StochLean_Probability_Process_Partition_CrossSums_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_F000
import Definitions.Def_SourceProof_24278e78a60501166c68bfc8
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_c3a38a53524388b4ac4c79ee
import Definitions.Def_SourceProof_db8eadde14e5caf2ba5d93ba
import Definitions.Def_SourceProof_ff07642989734d14cb2ac8eb

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
theorem _root_.Prove2MeSourceProof.h_d131488cf582eb29dc48ae9b
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).quadraticCovariationSumProcess X Y) atTop
      (hX.quadraticCovariation hY hF) := by
  have hu := (_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb ((_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb ((_root_.Prove2MeSourceProof.h_c3a38a53524388b4ac4c79ee ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) hY)) hF hπ))
    ((_root_.Prove2MeSourceProof.h_c3a38a53524388b4ac4c79ee hX) hF hπ)))
      ((_root_.Prove2MeSourceProof.h_c3a38a53524388b4ac4c79ee hY) hF hπ)
  simp only [_root_.Prove2MeSourceProof.h_db8eadde14e5caf2ba5d93ba]
  exact (_root_.Prove2MeSourceProof.h_24278e78a60501166c68bfc8 hu) (1 / 2 : ℝ)
end IsSemimartingale

end ProbabilityTheory


