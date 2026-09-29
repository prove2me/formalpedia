-- Prove2me | solution 1 for Algebra.Etale.existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/132415e8-a6be-5848-91ea-b26a8e2667ae

import Mathlib
import Theorems.Thm_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
import Theorems.Thm_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Etale_existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

universe u v w

namespace BHL

open Coalgebra

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem mem_map_maximalIdeal_of_one_tmul_eq_zero {B : Type*} [CommRing B] [Algebra R B] (y : B)
    (h : (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] y = (0 : IsLocalRing.ResidueField R ⊗[R] B)) :
    y ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R B) := by
  have h1 : TensorProduct.quotTensorEquivQuotSMul B (IsLocalRing.maximalIdeal R)
      ((1 : R ⧸ IsLocalRing.maximalIdeal R) ⊗ₜ[R] y) = 0 := by
    have h' : ((1 : R ⧸ IsLocalRing.maximalIdeal R) ⊗ₜ[R] y : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] B) = 0 := h
    rw [h', map_zero]
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map,
    Submodule.restrictScalars_mem] at h1
  exact h1

theorem sub_mem_maximalIdeal_of_algebraMap_eq {a b : R}
    (h : algebraMap R (IsLocalRing.ResidueField R) a = algebraMap R (IsLocalRing.ResidueField R) b) :
    a - b ∈ IsLocalRing.maximalIdeal R := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
  exact h

theorem counit_one_tmul {C : Type*} [CommRing C] [Bialgebra R C] (c : C) :
    Coalgebra.counit (R := IsLocalRing.ResidueField R) ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] c) =
      algebraMap R (IsLocalRing.ResidueField R) (Coalgebra.counit c) := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.algebraMap_eq_smul_one]

theorem comul_one_tmul {E : Type*} [CommRing E] [Bialgebra R E] (x : E) :
    Coalgebra.comul (R := IsLocalRing.ResidueField R) ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x) =
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R (IsLocalRing.ResidueField R) R (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R) E E
        (((1 : IsLocalRing.ResidueField R) ⊗ₜ[IsLocalRing.ResidueField R] (1 : IsLocalRing.ResidueField R)) ⊗ₜ[R] Coalgebra.comul x) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]

theorem map_tttComm_one_tmul {E C : Type*} [CommRing E] [Bialgebra R E] [CommRing C] [Bialgebra R C]
    (fbar : IsLocalRing.ResidueField R ⊗[R] E →ₐc[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] C)
    (ψ : E →ₐ[R] C)
    (hψx : ∀ x : E, fbar ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x) = (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] ψ x)
    (z : E ⊗[R] E) :
    TensorProduct.map (fbar : IsLocalRing.ResidueField R ⊗[R] E →ₗ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] C)
        (fbar : IsLocalRing.ResidueField R ⊗[R] E →ₗ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] C)
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R (IsLocalRing.ResidueField R) R (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R) E E
        (((1 : IsLocalRing.ResidueField R) ⊗ₜ[IsLocalRing.ResidueField R] (1 : IsLocalRing.ResidueField R)) ⊗ₜ[R] z)) =
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R (IsLocalRing.ResidueField R) R (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R) C C
        (((1 : IsLocalRing.ResidueField R) ⊗ₜ[IsLocalRing.ResidueField R] (1 : IsLocalRing.ResidueField R)) ⊗ₜ[R]
          Algebra.TensorProduct.map ψ ψ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, map_zero]
  | tmul a b =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    show fbar ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] a) ⊗ₜ[IsLocalRing.ResidueField R] fbar ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] b) = _
    rw [hψx, hψx]
  | add z w hz hw => simp only [TensorProduct.tmul_add, LinearEquiv.map_add, LinearMap.map_add, map_add, hz, hw]

theorem one_tmul_eq_zero_of_one_one_tmul_eq_zero {M : Type*} [AddCommGroup M] [Module R M] (m : M)
    (h : (((1 : IsLocalRing.ResidueField R) ⊗ₜ[IsLocalRing.ResidueField R] (1 : IsLocalRing.ResidueField R)) ⊗ₜ[R] m :
      (IsLocalRing.ResidueField R ⊗[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R) ⊗[R] M) = 0) :
    ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m : IsLocalRing.ResidueField R ⊗[R] M) = 0 := by
  have := congrArg (LinearMap.rTensor M ((TensorProduct.lid (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)).toLinearMap.restrictScalars R)) h
  rw [map_zero, LinearMap.rTensor_tmul] at this
  simpa using this

end BHL

open BHL in
theorem solution
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (E : Type v) [CommRing E] [Bialgebra R E] [Module.Finite R E] [Algebra.Etale R E]
    (C : Type w) [CommRing C] [Bialgebra R C] [Module.Finite R C]
    (fbar : IsLocalRing.ResidueField R ⊗[R] E →ₐc[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] C) :
    ∃! f : E →ₐc[R] C,
      Bialgebra.TensorProduct.map (BialgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) f = fbar := by
  classical

  obtain ⟨ψ, hψ, huniq⟩ :=
    Algebra.Etale.existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing R E C
      (fbar : IsLocalRing.ResidueField R ⊗[R] E →ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] C)
  have hψx : ∀ x : E, fbar ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x) = (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] ψ x := by
    intro x
    have := AlgHom.congr_fun hψ ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x)
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at this
    exact this.symm

  have hcounit : (Bialgebra.counitAlgHom R C).comp ψ = Bialgebra.counitAlgHom R E := by
    apply Algebra.Etale.algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing R E R
    intro x
    rw [Algebra.algebraMap_self, Ideal.map_id]
    apply sub_mem_maximalIdeal_of_algebraMap_eq
    show algebraMap R _ (Coalgebra.counit (ψ x)) = algebraMap R _ (Coalgebra.counit x)
    rw [← counit_one_tmul, ← counit_one_tmul (R := R) (C := E), ← hψx]
    exact CoalgHomClass.counit_comp_apply fbar _

  have hcomul : (Algebra.TensorProduct.map ψ ψ).comp (Bialgebra.comulAlgHom R E) = (Bialgebra.comulAlgHom R C).comp ψ := by
    apply Algebra.Etale.algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing R E (C ⊗[R] C)
    intro x
    apply mem_map_maximalIdeal_of_one_tmul_eq_zero
    apply one_tmul_eq_zero_of_one_one_tmul_eq_zero

    have h2 : TensorProduct.map (fbar : IsLocalRing.ResidueField R ⊗[R] E →ₗ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] C)
        (fbar : IsLocalRing.ResidueField R ⊗[R] E →ₗ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] C)
        (Coalgebra.comul ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x)) =
        Coalgebra.comul (fbar ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x)) :=
      LinearMap.congr_fun (CoalgHomClass.map_comp_comul fbar) ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x)
    rw [hψx, comul_one_tmul, comul_one_tmul, map_tttComm_one_tmul fbar ψ hψx] at h2
    have h3 := (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R (IsLocalRing.ResidueField R) R (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R) C C).injective h2
    show (((1 : IsLocalRing.ResidueField R) ⊗ₜ[IsLocalRing.ResidueField R] (1 : IsLocalRing.ResidueField R)) ⊗ₜ[R]
      (Algebra.TensorProduct.map ψ ψ (Coalgebra.comul x) - Coalgebra.comul (ψ x)) : _) = 0
    rw [TensorProduct.tmul_sub, h3, sub_self]

  let f : E →ₐc[R] C := BialgHom.ofAlgHom ψ hcounit hcomul
  have hf : (f : E →ₐ[R] C) = ψ := rfl
  refine ⟨f, ?_, ?_⟩
  · apply BialgHom.coe_algHom_injective
    rw [Bialgebra.TensorProduct.map_toAlgHom, BialgHom.id_toAlgHom, hf]
    exact hψ
  · intro g hg
    apply BialgHom.coe_algHom_injective
    rw [hf]
    apply huniq
    have := congrArg BialgHom.toAlgHom hg
    rw [Bialgebra.TensorProduct.map_toAlgHom, BialgHom.id_toAlgHom] at this
    exact this

end S_Algebra_Etale_existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
end P2MW
export P2MW.S_Algebra_Etale_existsUnique_bialgHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing (solution)
