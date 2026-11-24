-- Prove2me | solution 1 for AAInvW.subset_row_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:32:24.253088+00:00
-- url     : https://prove2.me/submissions/4d85f7b7-c079-4be1-939e-f9242c5f03af

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_esI_val
import Theorems.Thm_AAInvW_lf_S_rowStar

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
theorem _root_.solution : SsetRowStar := by
  unfold SsetRowStar
  intro k r z s hs a j hj
  have ha := a.isLt
  have hjl := j.isLt
  apply lf_S_rowStar k r z s hs a j
  by_contra hlt
  push_neg at hlt
  have hb : 2 * r + k - j.val < a.val := by omega
  apply hj ⟨2 * r + k - j.val, by omega⟩ hb
  apply Fin.ext
  rw [lf_esI_val]
  show j.val = 2 * r + k - (2 * r + k - j.val)
  omega
end AAInvW
