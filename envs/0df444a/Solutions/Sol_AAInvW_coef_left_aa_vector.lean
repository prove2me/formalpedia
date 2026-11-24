-- Prove2me | solution 1 for AAInvW.coef_left_aa_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:20:17.715913+00:00
-- url     : https://prove2.me/submissions/f69d22b9-45e7-4127-b2a4-db4975f00f06

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
import Theorems.Thm_AAInvW_lx_det_tri
import Theorems.Thm_AAInvW_lx_mulVec_apply
import Theorems.Thm_AAInvW_lx_mulVec_bvec
import Theorems.Thm_AAInvW_lx_sum_red
import Theorems.Thm_AAInvW_lx_eI_ne
import Theorems.Thm_AAInvW_lf_S_invCol
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
theorem _root_.solution : CoefLeftAAv := by
  unfold CoefLeftAAv
  intro k r z m hm s g B hs _
  have key : (Matrix.of fun a l : Fin m => ((s * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)) =
      (Matrix.of fun a b : Fin m => s⁻¹ (eI k r (Fin.castLE hm b)) (eI k r (Fin.castLE hm a))) *
      (Matrix.of fun a l : Fin m => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)) := by
    ext a l
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, lx_mulVec_apply]
    simp only [lx_mulVec_bvec]
    refine (lx_sum_red (fun b : Fin m => eI k r (Fin.castLE hm b)) ?_
      (fun j => g⁻¹ (B l) j * s⁻¹ j (eI k r (Fin.castLE hm a))) ?_).trans ?_
    · intro b b' h
      apply Fin.ext
      have h2 := congrArg Fin.val h
      simp only [lf_eI_val, Fin.coe_castLE] at h2
      exact h2
    · intro j hj
      show g⁻¹ (B l) j * s⁻¹ j (eI k r (Fin.castLE hm a)) = 0
      by_cases hle : (Fin.castLE hm a).val ≤ j.val
      · rw [lf_S_invCol k r z s hs (Fin.castLE hm a) j hle, if_neg, mul_zero]
        intro he
        exact hj ⟨a, he.symm⟩
      · exfalso
        apply hj
        push_neg at hle
        simp only [Fin.coe_castLE] at hle
        have := a.isLt
        refine ⟨⟨j.val, by omega⟩, ?_⟩
        apply Fin.ext
        simp only [lf_eI_val, Fin.coe_castLE, Fin.val_mk]
    · exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [key]
  apply lx_det_tri
  · intro a b hab
    have hab' : a.val < b.val := hab
    have hle : (Fin.castLE hm a).val ≤ (eI k r (Fin.castLE hm b)).val := by
      simp only [lf_eI_val, Fin.coe_castLE]
      omega
    rw [Matrix.of_apply, lf_S_invCol k r z s hs (Fin.castLE hm a) _ hle,
      if_neg (lx_eI_ne k r _ _ (by simp only [Fin.coe_castLE]; omega))]
  · intro a
    rw [Matrix.of_apply, lf_S_invCol k r z s hs (Fin.castLE hm a) _ (lf_eI_val k r _).ge, if_pos rfl]
end AAInvW
