-- Prove2me | solution 1 for Algebra.finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/9f66a4d0-aee0-5fc7-8707-19ecdf4005a4

import Mathlib
import Theorems.Thm_Algebra_exists_finite_free_algHom_tensorProduct_equiv_pi_of_algEquiv_pi
import Theorems.Thm_Algebra_exists_algHom_equiv_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace S17WRSplit

theorem exists_algEquiv_of_points_equiv
    (R : Type u) [CommRing R] (P : Type u) [CommRing P] [Algebra R P] (Q : Type u) [CommRing Q] [Algebra R Q]
    (η : ∀ (T : Type u) [CommRing T] [Algebra R T], (P →ₐ[R] T) ≃ (Q →ₐ[R] T))
    (hη : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T'] (u : T →ₐ[R] T')
      (f : P →ₐ[R] T), η T' (u.comp f) = u.comp (η T f)) :
    ∃ ψ : Q ≃ₐ[R] P, ∀ (T : Type u) [CommRing T] [Algebra R T] (f : P →ₐ[R] T),
      η T f = f.comp (ψ : Q →ₐ[R] P) := by
  set ψ₀ : Q →ₐ[R] P := η P (AlgHom.id R P) with hψ₀
  set θ : P →ₐ[R] Q := (η Q).symm (AlgHom.id R Q) with hθ
  have key : ∀ (T : Type u) [CommRing T] [Algebra R T] (f : P →ₐ[R] T), η T f = f.comp ψ₀ := by
    intro T _ _ f
    have := hη P T f (AlgHom.id R P)
    simpa [AlgHom.comp_id] using this
  have h₂ : θ.comp ψ₀ = AlgHom.id R Q := by
    have h : η Q θ = AlgHom.id R Q := by simp [hθ]
    rw [key] at h
    exact h
  have h₁ : ψ₀.comp θ = AlgHom.id R P := by
    apply (η P).injective
    rw [key, key, AlgHom.comp_assoc, h₂, AlgHom.comp_id, AlgHom.id_comp]
  refine ⟨AlgEquiv.ofAlgHom ψ₀ θ h₁ h₂, ?_⟩
  intro T _ _ f
  rw [key]
  rfl

theorem exists_points_baseChange_equiv
    (A : Type u) [CommRing A] (W : Type u) [CommRing W] [Algebra A W] (A' : Type u) [CommRing A'] [Algebra A A'] :
    ∃ β : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T],
        (A' ⊗[A] W →ₐ[A'] T) ≃ (W →ₐ[A] T),
      (∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T] (f : A' ⊗[A] W →ₐ[A'] T),
          β T f = (f.restrictScalars A).comp Algebra.TensorProduct.includeRight) ∧
      ∀ (T T' : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T]
        [CommRing T'] [Algebra A T'] [Algebra A' T'] [IsScalarTower A A' T'] (u : T →ₐ[A'] T')
        (f : A' ⊗[A] W →ₐ[A'] T), β T' (u.comp f) = (u.restrictScalars A).comp (β T f) := by
  refine ⟨fun T _ _ _ _ =>
    { toFun := fun f => (f.restrictScalars A).comp Algebra.TensorProduct.includeRight
      invFun := fun g => Algebra.TensorProduct.lift (Algebra.ofId A' T) g (fun _ _ => Commute.all _ _)
      left_inv := ?_
      right_inv := ?_ }, ?_, ?_⟩
  · intro f
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · ext w
      simp
  · intro g
    ext w
    simp
  · intro T _ _ _ _ f
    rfl
  · intro T T' _ _ _ _ _ _ _ _ u f
    rfl

end S17WRSplit

open S17WRSplit in
set_option maxHeartbeats 1600000 in

theorem solution
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (H : Type u) [CommRing H] [Algebra B H] [Module.Finite B H] [Module.Free B H]
    (W : Type u) [CommRing W] [Algebra A W]
    (e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)))
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
      (f : W →ₐ[A] T), e T' (u.comp f) = (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f))
    (A' : Type u) [CommRing A'] [Algebra A A'] (d : ℕ) (φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A')) :
    Module.Finite A' (A' ⊗[A] W) ∧ Module.Free A' (A' ⊗[A] W) := by
  classical
  obtain ⟨F, _, _, hFfin, hFfree, σ, hσnat⟩ :=
    Algebra.exists_finite_free_algHom_tensorProduct_equiv_pi_of_algEquiv_pi A B H A' d φ
  haveI : ∀ i, Module.Finite A' (F i) := hFfin
  haveI : ∀ i, Module.Free A' (F i) := hFfree
  obtain ⟨P, _, _, hPfin, hPfree, ε, hεnat⟩ := Algebra.exists_algHom_equiv_pi A' (Fin d) F
  obtain ⟨β, hβ, hβnat⟩ := exists_points_baseChange_equiv A W A'
  obtain ⟨ψ, -⟩ := exists_algEquiv_of_points_equiv A' (A' ⊗[A] W) P
    (fun T _ _ => by
      letI : Algebra A T := ((algebraMap A' T).comp (algebraMap A A')).toAlgebra
      haveI : IsScalarTower A A' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      exact (β T).trans ((e T).trans ((σ T).trans (ε T).symm)))
    (by
      intro T T' _ _ _ _ u f
      letI : Algebra A T := ((algebraMap A' T).comp (algebraMap A A')).toAlgebra
      haveI : IsScalarTower A A' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      letI : Algebra A T' := ((algebraMap A' T').comp (algebraMap A A')).toAlgebra
      haveI : IsScalarTower A A' T' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      simp only [Equiv.trans_apply]
      rw [hβnat, he_nat, hσnat]
      apply (ε T').injective
      rw [Equiv.apply_symm_apply, hεnat, Equiv.apply_symm_apply])
  haveI := hPfin; haveI := hPfree
  exact ⟨Module.Finite.equiv ψ.toLinearEquiv, Module.Free.of_equiv ψ.toLinearEquiv⟩

end S_Algebra_finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi
end P2MW
export P2MW.S_Algebra_finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi (solution)
