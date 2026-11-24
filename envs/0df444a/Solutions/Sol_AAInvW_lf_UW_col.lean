-- Prove2me | solution 1 for AAInvW.lf_UW_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:11:19.286785+00:00
-- url     : https://prove2.me/submissions/c7a4e3e0-d3d5-45d1-9307-da01bd7793f0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_col_of_mulVec
import Theorems.Thm_AAInvW_lf_bvec_apply

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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (a : Fin r) (t : Fin (2 * r + k + 1)) :
    h t (eI k r a) = if t = eI k r a then 1 else 0 := by
  exact (lf_col_of_mulVec (hh.2.1 a).1 t).trans (lf_bvec_apply _ _)
end AAInvW
