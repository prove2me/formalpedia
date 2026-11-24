-- Prove2me | solution 1 for AAInvW.lf_triInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:10:02.996196+00:00
-- url     : https://prove2.me/submissions/dc6b3878-f0c7-4e22-8f69-20d4278aa822

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Theorems.Thm_AAInvW_lf_eI_val

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
theorem _root_.solution (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hM : M⁻¹ * M = 1)
    (hU : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → M i (eI k r a) = if i = eI k r a then 1 else 0) :
    ∀ (a : ℕ) (ha : a < r) (i : Fin (2 * r + k + 1)), a ≤ i.val →
      M⁻¹ i (eI k r ⟨a, ha⟩) = if i = eI k r ⟨a, ha⟩ then 1 else 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro ha i hi
  have h1 := congrFun (congrFun hM i) (eI k r ⟨a, ha⟩)
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  rw [Finset.sum_eq_single (eI k r ⟨a, ha⟩)] at h1
  · rw [hU ⟨a, ha⟩ (eI k r ⟨a, ha⟩) (lf_eI_val k r ⟨a, ha⟩).ge, if_pos rfl, mul_one] at h1
    exact h1
  · intro t _ ht
    by_cases hat : a ≤ t.val
    · rw [hU ⟨a, ha⟩ t hat, if_neg ht, mul_zero]
    · push_neg at hat
      have htr : t.val < r := by omega
      have ht' : t = eI k r ⟨t.val, htr⟩ := Fin.ext (lf_eI_val k r ⟨t.val, htr⟩).symm
      rw [ht', ih t.val hat htr i (by omega), if_neg, zero_mul]
      intro hie
      have h3 := congrArg Fin.val hie
      rw [lf_eI_val] at h3
      simp only at h3
      omega
  · intro hn
    exact absurd (Finset.mem_univ _) hn
end AAInvW
