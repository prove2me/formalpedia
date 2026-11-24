-- Prove2me | solution 1 for AAInvW.lx_eI_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:10:03.805158+00:00
-- url     : https://prove2.me/submissions/0aa1e955-e0e9-4706-89bc-4aa9c3520a13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
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
theorem _root_.solution (k r : ℕ) (b c : Fin r) (h : b.val ≠ c.val) : eI k r b ≠ eI k r c := by
  intro he
  have h2 := congrArg Fin.val he
  rw [lf_eI_val, lf_eI_val] at h2
  exact h h2
end AAInvW
