-- Prove2me | solution 1 for AAInvW.left_aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:17.075409+00:00
-- url     : https://prove2.me/submissions/fdf02832-942b-40be-ae90-4fbebbc94762

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_LyQminorLeft
import Theorems.Thm_AAInvW_ly_qminor_left
import Theorems.Thm_AAInvW_coef_left_aa
import Theorems.Thm_AAInvW_coef_left_aa_vector


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
namespace AAInvW
theorem _root_.solution : LeftAA := by
  unfold LeftAA
  intro E _ _ k r z m hm u ell F s g hs hg
  constructor
  · simp only [AAop]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [ly_qminor_left, coef_left_aa k r z m hm s g c hs]
  · simp only [AAvop]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    rw [ly_qminor_left, coef_left_aa_vector k r z m hm s g B hs hg]
end AAInvW
