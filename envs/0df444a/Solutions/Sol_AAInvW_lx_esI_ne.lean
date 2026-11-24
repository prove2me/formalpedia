-- Prove2me | solution 1 for AAInvW.lx_esI_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:08:45.171233+00:00
-- url     : https://prove2.me/submissions/bc34dc06-71b5-43b2-9731-8f2d0aa0d61a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
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
theorem _root_.solution (k r : ℕ) (b c : Fin r) (h : b.val ≠ c.val) : esI k r b ≠ esI k r c := by
  intro he
  have h2 := congrArg Fin.val he
  rw [lf_esI_val, lf_esI_val] at h2
  have := b.isLt
  have := c.isLt
  omega
end AAInvW
