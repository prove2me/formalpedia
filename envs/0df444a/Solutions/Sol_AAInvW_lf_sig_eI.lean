-- Prove2me | solution 1 for AAInvW.lf_sig_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:14:25.02457+00:00
-- url     : https://prove2.me/submissions/c1d0f294-a169-4f74-8588-35950e1d31d6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_sig_val
import Theorems.Thm_AAInvW_lf_eI_val
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
theorem _root_.solution (k r : ℕ) (a : Fin r) : hkSig k r (eI k r a) = esI k r a := by
  apply Fin.ext
  rw [lf_sig_val, lf_esI_val, lf_eI_val]
  have h := a.isLt
  rw [if_neg (by omega)]
end AAInvW
