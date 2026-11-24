-- Prove2me | solution 1 for AAInvW.algebra_aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:36.901533+00:00
-- url     : https://prove2.me/submissions/47c082c5-de0a-4084-9aab-51b180036644

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdSmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
import Theorems.Thm_AAInvW_eI_inj
import Theorems.Thm_AAInvW_strictMono_val_iff
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
theorem _root_.solution : AlgAA := by
  intro A _ _ k r m hm E P Q xi u hE hQP hP
  classical
  have hrow : ∀ D : Fin m → Fin (2 * r + k + 1),
      qminor (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) (xR k r m hm) D u =
        ∑ d : Fin m → Fin (2 * r + k + 1), (∏ j, Q (D j) (d j)) • qminor E (xR k r m hm) d u := by
    intro D
    rw [q_expansion A _ m E P Q _ D u hQP]
    simp only [mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [show (∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, P (c j) (xR k r m hm j)) • (∏ j, Q (D j) (d j)) •
        qminor E c d u) = ∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, Q (D j) (d j)) •
        (∏ j, P (c j) (xR k r m hm j)) • qminor E c d u from
      Finset.sum_congr rfl (fun c _ => smul_comm _ _ _)]
    rw [← Finset.smul_sum]
    congr 1
    exact collapse hm (eI k r) (eI_inj k r) P hP (fun c => qminor E c d u)
      (fun c hc => by
        obtain ⟨p, q, hpq, h⟩ := not_inj hc
        exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c d u p q hpq h)
  simp only [hrow]
  have h1 : ∀ D : Fin m → Fin (2 * r + k + 1),
      (if StrictMono D then (Matrix.of fun a l : Fin m => xi a (D l)).det •
        ∑ d : Fin m → Fin (2 * r + k + 1), (∏ j, Q (D j) (d j)) • qminor E (xR k r m hm) d u else 0) =
      ∑ d : Fin m → Fin (2 * r + k + 1), (if StrictMono D then
        (Matrix.of fun a l : Fin m => xi a (D l)).det * ∏ j, Q (D j) (d j) else 0) •
          qminor E (xR k r m hm) d u := by
    intro D
    split_ifs
    · rw [Finset.smul_sum]; simp only [smul_smul]
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [grouping (fun i => i.val) Fin.val_injective (fun d => qminor E (xR k r m hm) d u)
    (fun d τ => quantumMinorColSkew_holds A _ m E hE (xR k r m hm) d τ u)
    (fun d hd => by
      obtain ⟨p, q, hpq, h⟩ := not_inj hd
      exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE (xR k r m hm) d u p q hpq h)]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  simp only [strictMono_val_iff]
  split_ifs with hC
  · congr 1
    have hM : (Matrix.of fun a l : Fin m => ∑ d, Q d (C l) * xi a d) =
        (Matrix.of fun a d => xi a d) * (Matrix.of fun d l => Q d (C l)) := by
      ext a l; simp [Matrix.mul_apply, mul_comm]
    rw [hM, cauchyBinet (fun i => i.val) Fin.val_injective]
    simp only [strictMono_val_iff, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun D _ => ?_)
    split_ifs with hD
    · simp only [Matrix.of_apply]
      rw [det_transpose_apply (Matrix.of fun i l => Q (D i) (C l)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [Matrix.of_apply, Function.comp_apply]
      ring
    · simp
  · rfl
end AAInvW
