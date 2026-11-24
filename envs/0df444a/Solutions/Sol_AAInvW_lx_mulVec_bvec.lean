-- Prove2me | solution 1 for AAInvW.lx_mulVec_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:11:20.938934+00:00
-- url     : https://prove2.me/submissions/86ee8780-f018-42ad-81c8-f130cba81409

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
import Theorems.Thm_AAInvW_lf_col_of_mulVec


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
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j i : Fin n) : (M *ᵥ bvec j) i = M i j := by
  exact (lf_col_of_mulVec rfl i).symm
end AAInvW
