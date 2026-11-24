-- Prove2me | solution 1 for AAInvW.lf_N_rowStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:54:00.99629+00:00
-- url     : https://prove2.me/submissions/8664cd7a-9144-46da-ae9b-588668e17b4a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_eI_val
import Theorems.Thm_AAInvW_lf_esI_val
import Theorems.Thm_AAInvW_lf_sig_eI
import Theorems.Thm_AAInvW_lf_eps_eI
import Theorems.Thm_AAInvW_lf_H_eI
import Theorems.Thm_AAInvW_lf_unit_entry
import Theorems.Thm_AAInvW_lf_sig_small

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
theorem _root_.solution (k r : ℕ) {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hm : m ∈ Formalism.QuantumDeterminants.Nset k r) : ∀ (b : ℕ) (hb : b < r) (p : Fin (2 * r + k + 1)), p.val ≤ 2 * r + k - b →
      m (esI k r ⟨b, hb⟩) p = if p = esI k r ⟨b, hb⟩ then 1 else 0 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro hb p hp
  have hU : inUH (Hpk k r) m := hm.1
  have hcol := hm.2.1 ⟨b, hb⟩
  have h2 := lf_unit_entry k r m hU (eI k r ⟨b, hb⟩) p
  rw [lf_H_eI] at h2
  rw [← h2, Finset.sum_eq_single (eI k r ⟨b, hb⟩)]
  · rw [hcol (eI k r ⟨b, hb⟩) (lf_eI_val k r ⟨b, hb⟩).ge, if_pos rfl, star_one, one_mul, lf_eps_eI,
      one_mul, lf_sig_eI]
  · intro t _ ht
    by_cases htb : b ≤ t.val
    · rw [hcol t htb, if_neg ht, star_zero, zero_mul]
    · push_neg at htb
      have htr : t.val < r := by omega
      rw [lf_sig_small k r t htr, ih t.val htb htr p (by omega), if_neg, mul_zero, mul_zero]
      intro hpe
      have h3 : p.val = 2 * r + k - t.val := by rw [hpe, lf_esI_val]
      omega
  · intro hn
    exact absurd (Finset.mem_univ _) hn
end AAInvW
