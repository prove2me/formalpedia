-- Prove2me | solution 1 for AAInvW.lf_unit_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:17:00.420372+00:00
-- url     : https://prove2.me/submissions/f68a0ae7-0006-4370-902a-896ccf03b52a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_Hmul

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
theorem _root_.solution (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : inUH (Hpk k r) g) (b p : Fin (2 * r + k + 1)) :
    ∑ t, star (g t b) * (hkEps k r t * g (hkSig k r t) p) = Hpk k r b p := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 := congrFun (congrFun h b) p
  rw [Matrix.mul_assoc, Matrix.mul_apply] at h2
  rw [← h2]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [lf_Hmul, Matrix.conjTranspose_apply]
end AAInvW
