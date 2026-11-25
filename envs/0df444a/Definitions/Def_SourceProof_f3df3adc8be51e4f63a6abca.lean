-- Prove2me | Definitions.Def_SourceProof_f3df3adc8be51e4f63a6abca
-- name    : SourceProof_f3df3adc8be51e4f63a6abca
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:47:48.189971+00:00
-- url     : https://prove2.me/theorems/32fd7e63-1bdd-5c50-9066-858828302da1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticCovariation_const_mul_left

import Definitions.Def_StochLean_Probability_Process_Partition_CrossSums_F000
import Definitions.Def_SourceProof_0f6a1de2f7189d335c4ff9a7
import Definitions.Def_SourceProof_24278e78a60501166c68bfc8
import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_4d91b341e83d2246d63e1ef9
import Definitions.Def_SourceProof_6443755938a3801e72d73393
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_d131488cf582eb29dc48ae9b

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bilinearity and version invariance of the canonical raw covariation

Linearity is inherited from the actual finite increment sums by uniqueness
of UCP limits. All comparisons are on one event for every time.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z X' Y' : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_f3df3adc8be51e4f63a6abca
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (c : ℝ) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) c).quadraticCovariation hY hF)
      (c • hX.quadraticCovariation hY hF) P := by
  apply (_root_.Prove2MeSourceProof.h_6443755938a3801e72d73393 ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) c)) hY hF
  · intro π hπ
    simpa only [_root_.Prove2MeSourceProof.h_4d91b341e83d2246d63e1ef9] using
      (_root_.Prove2MeSourceProof.h_24278e78a60501166c68bfc8 ((_root_.Prove2MeSourceProof.h_d131488cf582eb29dc48ae9b hX) hY hF hπ)) c
  · exact (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc ((_root_.Prove2MeSourceProof.h_0f6a1de2f7189d335c4ff9a7 hX) hY hF))
      (continuous_const.mul continuous_id)))
end IsSemimartingale

end ProbabilityTheory


