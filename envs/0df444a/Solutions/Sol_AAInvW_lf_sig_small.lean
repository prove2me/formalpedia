-- Prove2me | solution 1 for AAInvW.lf_sig_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:08:44.340977+00:00
-- url     : https://prove2.me/submissions/9c8d5337-a4b6-4f5b-b037-ae1710156f6f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_sig_val
import Theorems.Thm_AAInvW_lf_esI_val

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
theorem _root_.solution (k r : ℕ) (t : Fin (2 * r + k + 1)) (ht : t.val < r) :
    hkSig k r t = esI k r ⟨t.val, ht⟩ := by
  apply Fin.ext
  rw [lf_sig_val, lf_esI_val]
  rw [if_neg (by omega)]
end AAInvW
