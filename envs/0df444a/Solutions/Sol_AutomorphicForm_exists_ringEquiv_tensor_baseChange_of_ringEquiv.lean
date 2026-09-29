-- Prove2me | solution 1 for AutomorphicForm.exists_ringEquiv_tensor_baseChange_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c56f758d-bbc6-56e9-97cc-b1efe91a10a6

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_ringEquiv_tensor_baseChange_of_ringEquiv

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "toTensorGL sigmaTensor"
namespace BaseChangeIsoSol
p2m_open "AutomorphicForm"

open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

omit [FiniteDimensional K L] in

theorem repr_tmul (A : Type) [CommRing A] [Algebra K A]
    {ι : Type} (b : Module.Basis ι K L) (x : L) (a : A) (i : ι) :
    (TensorProduct.RightActions.Algebra.TensorProduct.basis A b).repr (x ⊗ₜ a) i =
      a * algebraMap K A (b.repr x i) := by
  simp [TensorProduct.RightActions.Algebra.TensorProduct.basis, Algebra.TensorProduct.basis_repr_tmul]

theorem continuous_of_tmul
    (A₁ : Type) [CommRing A₁] [Algebra K A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁]
    (A₂ : Type) [CommRing A₂] [Algebra K A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂]
    (f : A₁ →+* A₂) (hf : Continuous f) (hfK : ∀ k, f (algebraMap K A₁ k) = algebraMap K A₂ k)
    (F : L ⊗[K] A₁ →+ L ⊗[K] A₂) (hF : ∀ (x : L) (a : A₁), F (x ⊗ₜ a) = x ⊗ₜ f a) :
    Continuous F := by
  classical
  set b := Module.finBasis K L with hb
  set B₁ := TensorProduct.RightActions.Algebra.TensorProduct.basis A₁ b with hB₁
  set B₂ := TensorProduct.RightActions.Algebra.TensorProduct.basis A₂ b with hB₂

  let φ₁ := IsModuleTopology.continuousLinearEquiv B₁.equivFun
  let φ₂ := IsModuleTopology.continuousLinearEquiv B₂.equivFun
  let P : (Fin (Module.finrank K L) → A₁) → (Fin (Module.finrank K L) → A₂) := fun v i => f (v i)
  have hP : Continuous P := continuous_pi fun i => hf.comp (continuous_apply i)
  have key : ∀ z, F z = φ₂.symm (P (φ₁ z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [map_zero, map_zero]
        show (0 : L ⊗[K] A₂) = φ₂.symm (fun _ => f 0)
        rw [map_zero]
        exact (map_zero φ₂.symm).symm
    | tmul x a =>
        apply φ₂.injective
        rw [ContinuousLinearEquiv.apply_symm_apply, hF]
        funext i
        show B₂.equivFun (x ⊗ₜ f a) i = f (B₁.equivFun (x ⊗ₜ a) i)
        rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, repr_tmul, repr_tmul, map_mul, hfK]
    | add z₁ z₂ h₁ h₂ =>
        rw [map_add, h₁, h₂, map_add]
        have : P (φ₁ z₁ + φ₁ z₂) = P (φ₁ z₁) + P (φ₁ z₂) := by
          funext i; simp [P]
        rw [this, map_add]
  rw [show (F : L ⊗[K] A₁ → L ⊗[K] A₂) = fun z => φ₂.symm (P (φ₁ z)) from funext key]
  exact φ₂.symm.continuous.comp (hP.comp φ₁.continuous)

end AutomorphicForm.BaseChangeIsoSol

end

p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_exists_ringEquiv_tensor_baseChange_of_ringEquiv.AutomorphicForm"
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (A' : Type) [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
    (e : A ≃+* A') (he : Continuous e) (he' : Continuous e.symm) :
    letI : Algebra K A' := (e.toRingHom.comp (algebraMap K A)).toAlgebra
    ∃ E : L ⊗[K] A ≃+* L ⊗[K] A',
      Continuous E ∧ Continuous E.symm ∧
      (∀ (x : L) (a : A), E (x ⊗ₜ a) = x ⊗ₜ e a) ∧
      (∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K L A' σ (E z)) ∧
      (∀ g : GL (Fin 2) A, Matrix.GeneralLinearGroup.map E.toRingHom (toTensorGL K L A g) =
        toTensorGL K L A' (Matrix.GeneralLinearGroup.map e.toRingHom g)) := by
  letI instKA' : Algebra K A' := (e.toRingHom.comp (algebraMap K A)).toAlgebra

  let eK : A ≃ₐ[K] A' := AlgEquiv.ofRingEquiv (f := e) (fun k => rfl)
  let Ealg : L ⊗[K] A ≃ₐ[K] L ⊗[K] A' := Algebra.TensorProduct.congr AlgEquiv.refl eK
  have hEt : ∀ (x : L) (a : A), Ealg.toRingEquiv (x ⊗ₜ a) = x ⊗ₜ e a := fun x a => by
    show Ealg (x ⊗ₜ a) = x ⊗ₜ e a
    simp [Ealg, Algebra.TensorProduct.congr_apply, eK]
  have hEt' : ∀ (x : L) (a' : A'), Ealg.toRingEquiv.symm (x ⊗ₜ a') = x ⊗ₜ e.symm a' := fun x a' => by
    apply Ealg.toRingEquiv.injective
    rw [RingEquiv.apply_symm_apply, hEt, RingEquiv.apply_symm_apply]
  refine ⟨Ealg.toRingEquiv, ?_, ?_, hEt, ?_, ?_⟩
  · exact AutomorphicForm.BaseChangeIsoSol.continuous_of_tmul K L A A' e.toRingHom he (fun k => rfl)
      Ealg.toRingEquiv.toAddMonoidHom (fun x a => hEt x a)
  · refine AutomorphicForm.BaseChangeIsoSol.continuous_of_tmul K L A' A e.symm.toRingHom he' ?_
      Ealg.toRingEquiv.symm.toAddMonoidHom (fun x a' => hEt' x a')
    intro k
    show e.symm (e (algebraMap K A k)) = algebraMap K A k
    exact e.symm_apply_apply _
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x a =>
        simp only [sigmaTensor, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
          AlgHom.coe_id, id_eq]
        rw [hEt, show ((σ : L ≃ₐ[K] L) : L →ₐ[K] L) x = σ x from rfl, hEt]
        simp [Algebra.TensorProduct.map_tmul]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  · intro g
    ext i j
    simp only [toTensorGL, Matrix.GeneralLinearGroup.map_apply]
    show Ealg.toRingEquiv (Algebra.TensorProduct.includeRight ((g : Matrix (Fin 2) (Fin 2) A) i j)) =
      Algebra.TensorProduct.includeRight (e ((g : Matrix (Fin 2) (Fin 2) A) i j))
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply, hEt]

end S_AutomorphicForm_exists_ringEquiv_tensor_baseChange_of_ringEquiv
end P2MW
export P2MW.S_AutomorphicForm_exists_ringEquiv_tensor_baseChange_of_ringEquiv (solution)
