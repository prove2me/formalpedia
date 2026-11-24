-- Prove2me | solution 1 for AAInvW.coef_left_aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:49:42.964676+00:00
-- url     : https://prove2.me/submissions/a6bc436d-c252-4ef3-83b8-49453ba25e6e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
import Theorems.Thm_AAInvW_lx_det_tri
import Theorems.Thm_AAInvW_lx_mulVec_apply
import Theorems.Thm_AAInvW_lx_herm_eI
import Theorems.Thm_AAInvW_lx_sum_red
import Theorems.Thm_AAInvW_lx_esI_ne
import Theorems.Thm_AAInvW_lf_esI_val
import Theorems.Thm_AAInvW_subset_row_star


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
theorem _root_.solution : CoefLeftAA := by
  intro k r z m hm s g c hs
  have hrow := subset_row_star k r z s hs
  have inj : Function.Injective (fun b : Fin m => esI k r (Fin.castLE hm b)) := by
    intro b b' h
    have := b.isLt; have := b'.isLt
    have := congrArg Fin.val h
    simp only [lf_esI_val, Fin.val_castLE] at this
    exact Fin.ext (by omega)
  have key : ∀ (a l : Fin m), herm (Hpk k r) ((s * g) *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a))) =
      ∑ b : Fin m, s (esI k r (Fin.castLE hm a)) (esI k r (Fin.castLE hm b)) *
        herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm b))) := by
    intro a l
    simp only [lx_herm_eI]
    rw [← mulVec_mulVec, lx_mulVec_apply]
    refine lx_sum_red (fun b : Fin m => esI k r (Fin.castLE hm b)) inj _ ?_
    intro j hj
    have h0 : s (esI k r (Fin.castLE hm a)) j = 0 := by
      have hc : ∀ b : Fin r, b.val < (Fin.castLE hm a).val → j ≠ esI k r b := by
        intro b hb he
        apply hj
        refine ⟨⟨b.val, by simp only [Fin.val_castLE] at hb; omega⟩, ?_⟩
        rw [he]; rfl
      rw [hrow _ j hc, if_neg]
      intro he; exact hj ⟨a, he.symm⟩
    rw [h0, zero_mul]
  have hM : (Matrix.of fun a l : Fin m => herm (Hpk k r) ((s * g) *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))) =
      (Matrix.of fun a b : Fin m => s (esI k r (Fin.castLE hm a)) (esI k r (Fin.castLE hm b))) *
      (Matrix.of fun a l : Fin m => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))) := by
    ext a l
    simp only [of_apply, mul_apply, key]
  rw [hM]
  apply lx_det_tri
  · intro a b hab
    simp only [of_apply]
    have hab' : a.val < b.val := hab
    rw [hrow _ _ ?_, if_neg]
    · exact lx_esI_ne k r _ _ (by simp only [Fin.val_castLE]; omega)
    · intro c hc
      exact lx_esI_ne k r _ _ (by simp only [Fin.val_castLE] at hc ⊢; omega)
  · intro a
    simp only [of_apply]
    rw [hrow _ _ ?_, if_pos rfl]
    intro c hc
    exact lx_esI_ne k r _ _ (by omega)
end AAInvW
