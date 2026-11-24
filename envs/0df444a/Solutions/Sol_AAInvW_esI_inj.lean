-- Prove2me | solution 1 for AAInvW.esI_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:59:42.579722+00:00
-- url     : https://prove2.me/submissions/2ae37a70-4e7b-4e93-a4b9-8df87ad65220

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
theorem _root_.solution (k r : ℕ) : Function.Injective (esI k r) := by
  unfold esI
  intro a b h
  have h1 := congrArg Fin.val h
  simp only at h1
  have ha := a.isLt
  have hb := b.isLt
  exact Fin.ext (by omega)
end AAInvW
