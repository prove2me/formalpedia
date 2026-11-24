-- Prove2me | solution 1 for AAInvW.hk_eps_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:59:52.419228+00:00
-- url     : https://prove2.me/submissions/d8c56f23-e791-4313-9f32-4b0b7051b397

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose

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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : hkEps k r i * hkEps k r i = 1 := by
  unfold hkEps
  split_ifs <;> norm_num
end AAInvW
