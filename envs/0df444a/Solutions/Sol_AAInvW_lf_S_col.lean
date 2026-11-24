-- Prove2me | solution 1 for AAInvW.lf_S_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:31:29.74041+00:00
-- url     : https://prove2.me/submissions/691cf584-e700-4f5e-aca6-830e68272571

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_eI_val
import Theorems.Thm_AAInvW_lf_UW_col

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
    s i (eI k r a) = if i = eI k r a then 1 else 0 := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
  · rw [hm.2.1 a (eI k r a) (lf_eI_val k r a).ge, if_pos rfl, mul_one, lf_UW_col k r z hh a i]
  · intro t _ ht
    by_cases hat : a.val ≤ t.val
    · rw [hm.2.1 a t hat, if_neg ht, mul_zero]
    · push_neg at hat
      have htr : t.val < r := by have := a.isLt; omega
      have ht' : t = eI k r ⟨t.val, htr⟩ := Fin.ext (lf_eI_val k r ⟨t.val, htr⟩).symm
      rw [ht', lf_UW_col k r z hh ⟨t.val, htr⟩ i, if_neg, zero_mul]
      intro hie
      have h3 := congrArg Fin.val hie
      rw [lf_eI_val] at h3
      simp only at h3
      omega
  · intro hn
    exact absurd (Finset.mem_univ _) hn
end AAInvW
