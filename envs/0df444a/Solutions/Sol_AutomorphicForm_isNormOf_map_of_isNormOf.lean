-- Prove2me | solution 1 for AutomorphicForm.isNormOf_map_of_isNormOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3168c6af-6499-5275-92a7-b3b360771b10

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isNormOf_map_of_isNormOf

set_option autoImplicit false

open scoped TensorProduct

namespace R3FafNormLoc

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A B : Type) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (g : A →ₐ[K] B)
  (σ : L ≃ₐ[K] L)

noncomputable def coeffMap : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] B) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.map (AlgHom.id K L) g).toRingHom

theorem coeffMap_apply (x : GL (Fin 2) (L ⊗[K] A)) :
    coeffMap K L A B g x =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.map (AlgHom.id K L) g).toRingHom x := rfl

theorem map_sigmaTensor (t : L ⊗[K] A) :
    (Algebra.TensorProduct.map (AlgHom.id K L) g) (AutomorphicForm.sigmaTensor K L A σ t) =
      AutomorphicForm.sigmaTensor K L B σ ((Algebra.TensorProduct.map (AlgHom.id K L) g) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp [AutomorphicForm.sigmaTensor]
  | tmul l a =>
      simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

theorem map_includeRight (a : A) :
    (Algebra.TensorProduct.map (AlgHom.id K L) g)
        ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a) =
      (Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B) (g a) := by
  simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem coeffMap_sigmaGL (x : GL (Fin 2) (L ⊗[K] A)) :
    coeffMap K L A B g (AutomorphicForm.sigmaGL K L A σ x) =
      AutomorphicForm.sigmaGL K L B σ (coeffMap K L A B g x) := by
  ext i j
  exact map_sigmaTensor K L A B g σ (x.val i j)

theorem coeffMap_toTensorGL (γ : GL (Fin 2) A) :
    coeffMap K L A B g (AutomorphicForm.toTensorGL K L A γ) =
      AutomorphicForm.toTensorGL K L B (Matrix.GeneralLinearGroup.map g.toRingHom γ) := by
  ext i j
  exact map_includeRight K L A B g (γ.val i j)

theorem coeffMap_iterate_sigmaGL (i : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) :
    coeffMap K L A B g ((⇑(AutomorphicForm.sigmaGL K L A σ))^[i] x) =
      (⇑(AutomorphicForm.sigmaGL K L B σ))^[i] (coeffMap K L A B g x) := by
  have h : Function.Semiconj (coeffMap K L A B g) (AutomorphicForm.sigmaGL K L A σ)
      (AutomorphicForm.sigmaGL K L B σ) := fun z => coeffMap_sigmaGL K L A B g σ z
  exact (h.iterate_right i) x

theorem coeffMap_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    coeffMap K L A B g (AutomorphicForm.normString K L A σ δ) =
      AutomorphicForm.normString K L B σ (coeffMap K L A B g δ) := by
  unfold AutomorphicForm.normString
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact coeffMap_iterate_sigmaGL K L A B g σ i δ

end R3FafNormLoc

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (A B : Type) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (g : A →ₐ[K] B)
    (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormOf K L A σ γ δ) :
    AutomorphicForm.IsNormOf K L B σ (Matrix.GeneralLinearGroup.map g.toRingHom γ)
      (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.map (AlgHom.id K L) g).toRingHom δ) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨R3FafNormLoc.coeffMap K L A B g y, ?_⟩
  unfold AutomorphicForm.IsNormConjugator at hy ⊢

  have key := congrArg (R3FafNormLoc.coeffMap K L A B g) hy
  rw [R3FafNormLoc.coeffMap_toTensorGL] at key
  rw [key, map_mul, map_mul, map_inv, R3FafNormLoc.coeffMap_normString]
  rfl

end S_AutomorphicForm_isNormOf_map_of_isNormOf
end P2MW
export P2MW.S_AutomorphicForm_isNormOf_map_of_isNormOf (solution)
