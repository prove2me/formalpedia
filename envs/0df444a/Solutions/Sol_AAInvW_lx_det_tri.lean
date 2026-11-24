-- Prove2me | solution 1 for AAInvW.lx_det_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:22:49.562916+00:00
-- url     : https://prove2.me/submissions/18eb830b-be26-4f2d-bd42-ce3c2475c246

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector

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
theorem _root_.solution {m : ℕ} (T N : Matrix (Fin m) (Fin m) ℂ) (hT : ∀ a b : Fin m, a < b → T a b = 0)
    (hd : ∀ a, T a a = 1) : (T * N).det = N.det := by
  rw [Matrix.det_mul, Matrix.det_of_lowerTriangular T (by
      intro i j hij
      exact hT i j (OrderDual.toDual_lt_toDual.mp hij)), Finset.prod_eq_one (fun a _ => hd a), one_mul]
end AAInvW
