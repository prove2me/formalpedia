-- Prove2me | solution 1 for AAInvW.subset_inverse_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:20:40.113041+00:00
-- url     : https://prove2.me/submissions/fb392e31-26fc-450e-80cd-d029983f7cb0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_eI_val
import Theorems.Thm_AAInvW_lf_S_invCol

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
theorem _root_.solution : SsetInvCol := by
  unfold SsetInvCol
  intro k r z s hs a i hi
  apply lf_S_invCol k r z s hs a i
  by_contra hlt
  push_neg at hlt
  have ha := a.isLt
  exact hi ⟨i.val, by omega⟩ hlt (Fin.ext (lf_eI_val k r ⟨i.val, by omega⟩).symm)
end AAInvW
