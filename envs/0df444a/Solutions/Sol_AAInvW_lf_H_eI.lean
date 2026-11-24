-- Prove2me | solution 1 for AAInvW.lf_H_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:34:43.862578+00:00
-- url     : https://prove2.me/submissions/e61a8ef7-ea48-4a0c-bdcf-5ab503206bcf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_sig_eI
import Theorems.Thm_AAInvW_lf_eps_eI
import Theorems.Thm_AAInvW_hk_apply


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
theorem _root_.solution (k r : ℕ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) q = if q = esI k r a then 1 else 0 := by
  rw [hk_apply, lf_sig_eI, lf_eps_eI]
end AAInvW
