-- Prove2me | solution 1 for AAInvW.eI_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:03:20.822563+00:00
-- url     : https://prove2.me/submissions/7c485c96-c2a6-45b4-be53-005c97c737b3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdSmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply

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
theorem _root_.solution (k r : ℕ) : Function.Injective (eI k r) := by
  unfold eI
  intro a b h
  have h1 := congrArg Fin.val h
  simp only at h1
  exact Fin.ext h1
end AAInvW
