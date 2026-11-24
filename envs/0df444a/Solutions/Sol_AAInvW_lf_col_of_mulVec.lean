-- Prove2me | solution 1 for AAInvW.lf_col_of_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:52:45.581117+00:00
-- url     : https://prove2.me/submissions/c1e78b58-a355-46f1-b8f2-9988458913de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg

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
theorem _root_.solution {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {j : Fin n} {v : Fin n → ℂ}
    (h : M *ᵥ bvec j = v) (t : Fin n) : M t j = v t := by
  rw [← h]
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
end AAInvW
