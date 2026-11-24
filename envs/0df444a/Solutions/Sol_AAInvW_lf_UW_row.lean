-- Prove2me | solution 1 for AAInvW.lf_UW_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:54:01.812811+00:00
-- url     : https://prove2.me/submissions/ad371057-5fbc-462d-9155-cba4ceb2416d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_sig_eI
import Theorems.Thm_AAInvW_lf_eps_eI
import Theorems.Thm_AAInvW_lf_H_eI
import Theorems.Thm_AAInvW_lf_unit_entry
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
    (hh : h ∈ UWset k r z) (a : Fin r) (p : Fin (2 * r + k + 1)) :
    h (esI k r a) p = if p = esI k r a then 1 else 0 := by
  obtain ⟨hU, hv, -⟩ := hh
  have hcol : ∀ t, h t (eI k r a) = if t = eI k r a then 1 else 0 := fun t => by
    rw [lf_col_of_mulVec (hv a).1 t, lf_bvec_apply]
  have h2 := lf_unit_entry k r h (show inUH (Hpk k r) h from hU) (eI k r a) p
  rw [lf_H_eI] at h2
  rw [← h2, Finset.sum_eq_single (eI k r a)]
  · rw [hcol, if_pos rfl, star_one, one_mul, lf_eps_eI, one_mul, lf_sig_eI]
  · intro t _ ht
    rw [hcol, if_neg ht, star_zero, zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn
end AAInvW
