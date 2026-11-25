-- Prove2me | Definitions.Def_SourceProof_bd5db35608e4f06856d6b838
-- name    : SourceProof_bd5db35608e4f06856d6b838
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:08.023549+00:00
-- url     : https://prove2.me/theorems/b70cb885-67c7-4ae9-b37b-5041957629d1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPredictableStoppingTime.restrictedStoppingTime_before

import Definitions.Def_StochLean_Probability_Process_Filtration_StoppingTimeReindex_F000
import Definitions.Def_SourceProof_1c06092a52aed18ba3f491de
import Definitions.Def_SourceProof_51740884f3e4929ebdd46661
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_6744ca81945b1a55b21c8156
import Definitions.Def_SourceProof_aac175930a79ec503e2de8ac

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Restriction of predictable times to pre-stopping events

For `A ∈ F_(T-)`, Levy upward convergence along an announcing filtration gives
eventually correct stopped-measurable event approximations. Tail infima and
integer caps construct announcing data for `T_A`. No general `F_T` event is
substituted for the stronger pre-stopping measurability hypothesis.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {τ : Ω → WithTop ℝ≥0}

namespace IsPredictableStoppingTime
theorem _root_.Prove2MeSourceProof.h_bd5db35608e4f06856d6b838
    (hp : IsPredictableStoppingTime F τ P) (hF : F.IsUsual P) {A : Set Ω}
    (hA : MeasurableSet[hp.1.measurableSpaceBefore] A) :
    IsPredictableStoppingTime F (restrictedStoppingTime τ A) P := by
  obtain ⟨σ, hs⟩ := hp.2
  let G := F.stoppingTimeReindex σ hs.isStoppingTime (fun _ _ hij ω ↦ hs.monotone ω hij)
  have hAG : MeasurableSet[⨆ n, G n] A := by
    rw [(_root_.Prove2MeSourceProof.h_1c06092a52aed18ba3f491de hs) hp.1 (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF)] at hA
    exact hA
  obtain ⟨B, hB, hBA⟩ := (_root_.Prove2MeSourceProof.h_6744ca81945b1a55b21c8156 (P := P) G) hAG
  exact (_root_.Prove2MeSourceProof.h_aac175930a79ec503e2de8ac hs) hp.1 hF
    ((_root_.Prove2MeSourceProof.h_51740884f3e4929ebdd46661 hp.1) A hA) hB hBA
end IsPredictableStoppingTime

end ProbabilityTheory


