-- Prove2me | solution 1 for AAInvW.q_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:54.551043+00:00
-- url     : https://prove2.me/submissions/5e8dab31-c255-41a4-98ef-296d5b914980

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdSmul
import Theorems.Thm_AAInvW_ofFn_prod_sum
import Theorems.Thm_AAInvW_ofFn_prod_smul
import Theorems.Thm_AAInvW_tm_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
noncomputable section
namespace AAInvW
open Formalism.REAL
private theorem sum_perm_mul_sum_prod_smul_eq_sum_sum {A : Type*} [Ring A] [Algebra ℂ A] {t n : ℕ}
    (s : Equiv.Perm (Fin t) → A) (w1 : Fin n → Fin t → ℂ) (w2 : Fin t → Fin n → ℂ)
    (G : (Fin t → Fin n) → (Fin t → Fin n) → A) :
    ∑ σ : Equiv.Perm (Fin t), s σ * ∑ cd : Fin t → Fin n × Fin n,
        (∏ k, w1 (cd k).1 (σ k) * w2 k (cd k).2) • G (fun k => (cd k).1) (fun k => (cd k).2) =
      ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n, ((∏ j, w1 (c j) j) * ∏ j, w2 j (d j)) •
        ∑ σ : Equiv.Perm (Fin t), s σ * G (fun k => c (σ k)) d := by
  have h1 : ∀ σ : Equiv.Perm (Fin t), ∑ cd : Fin t → Fin n × Fin n,
      (∏ k, w1 (cd k).1 (σ k) * w2 k (cd k).2) • G (fun k => (cd k).1) (fun k => (cd k).2) =
      ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n, ((∏ j, w1 (c j) j) * ∏ j, w2 j (d j)) •
        G (fun k => c (σ k)) d := by
    intro σ
    rw [← (Equiv.arrowProdEquivProdArrow _ _ _).symm.sum_comp, Fintype.sum_prod_type]
    rw [← (Equiv.arrowCongr σ.symm (Equiv.refl (Fin n))).sum_comp]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.arrowCongr_apply, Equiv.symm_symm,
      Equiv.coe_refl, Equiv.coe_fn_symm_mk, Function.comp_apply, id]
    congr 1
    rw [Finset.prod_mul_distrib]
    congr 1
    exact Equiv.prod_comp σ (fun j => w1 (c j) j)
  simp only [h1, Finset.mul_sum, Finset.smul_sum, mul_smul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
end AAInvW
end
end

set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL
namespace AAInvW
theorem _root_.solution : QExpand := by
  unfold QExpand
  intro A _ _ n t E P Q a b u hQP
  simp only [qminor]
  simp only [tm_conj E P Q hQP, ofFn_prod_sum, ofFn_prod_smul]
  exact sum_perm_mul_sum_prod_smul_eq_sum_sum (fun σ => ((Equiv.Perm.sign σ : ℤ) : A)) (fun x j => P x (a j))
    (fun k y => Q (b k) y) (fun c1 d => (List.ofFn fun k => Tm E (u - ((k : ℕ) : ℂ)) (c1 k) (d k)).prod)
end AAInvW
