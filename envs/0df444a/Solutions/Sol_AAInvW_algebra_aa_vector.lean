-- Prove2me | solution 1 for AAInvW.algebra_aa_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:37.765803+00:00
-- url     : https://prove2.me/submissions/e2df92c4-584c-4712-a327-99c4737e22d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdSmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
import Theorems.Thm_AAInvW_esI_inj
import Theorems.Thm_AAInvW_keyS_inj
import Theorems.Thm_AAInvW_not_inj
import Theorems.Thm_AAInvW_det_transpose_apply
import Theorems.Thm_AAInvW_cauchyBinet
import Theorems.Thm_AAInvW_collapse
import Theorems.Thm_AAInvW_grouping
import Theorems.Thm_AAInvW_q_expansion
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds
import Theorems.Thm_Formalism_REAL_quantumMinorRowSkew_holds
import Theorems.Thm_Formalism_REAL_quantumMinor_eq_zero_of_col_eq
import Theorems.Thm_Formalism_REAL_quantumMinor_eq_zero_of_row_eq


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
theorem _root_.solution : AlgAAv := by
  intro A _ _ k r m hm E P Q eta v hE hQP hQ
  classical
  have hcol : ∀ B : Fin m → Fin (2 * r + k + 1),
      qminor (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) B (sR k r m hm) v =
        ∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, P (c j) (B j)) • qminor E c (sR k r m hm) v := by
    intro B
    rw [q_expansion A _ m E P Q B _ v hQP]
    simp only [mul_smul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.smul_sum]
    congr 1
    exact collapse hm (esI k r) (esI_inj k r) (fun i j => Q j i) hQ (fun d => qminor E c d v)
      (fun d hd => by
        obtain ⟨p, q, hpq, h⟩ := not_inj hd
        exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE c d v p q hpq h)
  simp only [hcol]
  have h1 : ∀ B : Fin m → Fin (2 * r + k + 1),
      (if StrictMono (fun l => keyS k r (B l)) then (Matrix.of fun a l : Fin m => eta a (B l)).det •
        ∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, P (c j) (B j)) • qminor E c (sR k r m hm) v else 0) =
      ∑ c : Fin m → Fin (2 * r + k + 1), (if StrictMono (fun l => keyS k r (B l)) then
        (Matrix.of fun a l : Fin m => eta a (B l)).det * ∏ j, P (c j) (B j) else 0) •
          qminor E c (sR k r m hm) v := by
    intro B
    split_ifs
    · rw [Finset.smul_sum]; simp only [smul_smul]
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [grouping (keyS k r) (keyS_inj k r) (fun c => qminor E c (sR k r m hm) v)
    (fun c τ => quantumMinorRowSkew_holds A _ m E c (sR k r m hm) τ v)
    (fun c hc => by
      obtain ⟨p, q, hpq, h⟩ := not_inj hc
      exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c (sR k r m hm) v p q hpq h)]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  split_ifs with hC
  · congr 1
    have hM : (Matrix.of fun a l : Fin m => ∑ d, P (C l) d * eta a d) =
        (Matrix.of fun a d => eta a d) * (Matrix.of fun d l => P (C l) d) := by
      ext a l; simp [Matrix.mul_apply, mul_comm]
    rw [hM, cauchyBinet (keyS k r) (keyS_inj k r)]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    split_ifs with hB
    · simp only [Matrix.of_apply]
      rw [det_transpose_apply (Matrix.of fun i l => P (C l) (B i)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [Matrix.of_apply, Function.comp_apply]
      ring
    · simp
  · rfl
end AAInvW
