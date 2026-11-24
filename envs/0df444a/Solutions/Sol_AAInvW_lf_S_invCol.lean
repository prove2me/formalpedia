-- Prove2me | solution 1 for AAInvW.lf_S_invCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:00:33.44144+00:00
-- url     : https://prove2.me/submissions/b8212542-6d75-4040-aabc-d671b94c366c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_det_ne_zero
import Theorems.Thm_AAInvW_subset_upper_hessenberg
import Theorems.Thm_AAInvW_lf_S_col
import Theorems.Thm_AAInvW_lf_triInv

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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hs : s ∈ Sset k r z) (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) :
    s⁻¹ i (eI k r a) = if i = eI k r a then 1 else 0 := by
  have hUH : inUH (Hpk k r) s := subset_upper_hessenberg k r z s hs
  have hdet : IsUnit s.det := isUnit_iff_ne_zero.mpr (lf_det_ne_zero k r hUH)
  exact lf_triInv k r s (Matrix.nonsing_inv_mul s hdet) (fun b i' hb => lf_S_col k r z s hs b i' hb)
    a.val a.isLt i hi
end AAInvW
