-- Prove2me | solution 1 for AAInvW.lf_S_rowStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:39.92795+00:00
-- url     : https://prove2.me/submissions/0bf4efce-ebcb-4670-89cd-cef626355f0e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_UW_row
import Theorems.Thm_AAInvW_lf_N_rowStar

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
    (hs : s ∈ Sset k r z) (a : Fin r) (j : Fin (2 * r + k + 1)) (hj : j.val ≤ 2 * r + k - a.val) :
    s (esI k r a) j = if j = esI k r a then 1 else 0 := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  rw [Matrix.mul_apply, Finset.sum_eq_single (esI k r a)]
  · rw [lf_UW_row k r z hh a, if_pos rfl, one_mul]
    exact lf_N_rowStar k r hm a.val a.isLt j hj
  · intro t _ ht
    rw [lf_UW_row k r z hh a, if_neg ht, zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn
end AAInvW
