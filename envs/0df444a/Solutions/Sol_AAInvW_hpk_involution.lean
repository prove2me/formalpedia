-- Prove2me | solution 1 for AAInvW.hpk_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:46:35.846785+00:00
-- url     : https://prove2.me/submissions/56b44351-76ac-40f3-b51c-1391a2acb9ab

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Theorems.Thm_AAInvW_hk_mul_self
import Theorems.Thm_AAInvW_hk_conjTranspose

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
theorem _root_.solution : HpkInvol := fun k r => ⟨hk_conjTranspose k r, hk_mul_self k r⟩
end AAInvW
