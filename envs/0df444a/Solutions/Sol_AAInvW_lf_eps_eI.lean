-- Prove2me | solution 1 for AAInvW.lf_eps_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:07:19.403409+00:00
-- url     : https://prove2.me/submissions/313adc94-c28e-438f-a399-3c461ea9961d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_eI_val

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
theorem _root_.solution (k r : ℕ) (a : Fin r) : hkEps k r (eI k r a) = 1 := by
  have h := a.isLt
  unfold hkEps
  rw [if_neg (by rw [lf_eI_val]; omega)]
end AAInvW
