-- Prove2me | solution 1 for Algebra.Etale.exists_faithfullyFlat_forall_nonempty_algEquiv_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a3098978-f017-50d7-8680-8cde4bc10e86

import Mathlib
import Theorems.Thm_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Etale_exists_faithfullyFlat_forall_nonempty_algEquiv_pi

set_option autoImplicit false

open TensorProduct

universe u

namespace CSplitAux

theorem nonempty_algEquiv_pi_of_algHom {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    {T₁ T : Type u} [CommRing T₁] [CommRing T] [Algebra R T₁] [Algebra R T] (φ : T₁ →ₐ[R] T)
    {n : ℕ} (e : T₁ ⊗[R] S ≃ₐ[T₁] (Fin n → T₁)) : Nonempty (T ⊗[R] S ≃ₐ[T] (Fin n → T)) := by
  letI : Algebra T₁ T := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R T₁ T := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  exact ⟨(Algebra.TensorProduct.cancelBaseChange R T₁ T T S).symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) e).trans <|
    (Algebra.TensorProduct.piRight T₁ T T (fun _ : Fin n => T₁)).trans <|
    AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.rid T₁ T T⟩

def P (ι : Type) : Prop :=
  ∀ (R : Type u) [CommRing R] (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Finite R (B i)] [∀ i, Algebra.Etale R (B i)]
    (deg : ι → ℕ) (_ : ∀ i, Module.rankAtStalk (R := R) (B i) = deg i),
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
      Module.Finite R R' ∧ Algebra.Etale R R' ∧ Module.FaithfullyFlat R R' ∧
      ∀ i, Nonempty (R' ⊗[R] (B i) ≃ₐ[R'] (Fin (deg i) → R'))

theorem P_of_equiv {α β : Type} (e : α ≃ β) (h : P.{u} α) : P.{u} β := by
  intro R _ B _ _ _ _ deg hdeg
  obtain ⟨R', _, _, h1, h2, h3, h4⟩ := h R (fun a => B (e a)) (fun a => deg (e a)) (fun a => hdeg (e a))
  refine ⟨R', inferInstance, inferInstance, h1, h2, h3, fun b => ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective b
  exact h4 a

theorem P_empty : P.{u} PEmpty := by
  intro R _ B _ _ _ _ deg hdeg
  exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, fun i => i.elim⟩

theorem P_option {α : Type} [Fintype α] (h : P.{u} α) : P.{u} (Option α) := by
  intro R _ B _ _ _ _ deg hdeg
  obtain ⟨R₁, _, _, fin₁, et₁, ff₁, hs₁⟩ :=
    h R (fun a => B (some a)) (fun a => deg (some a)) (fun a => hdeg (some a))
  obtain ⟨T, _, _, finT, etT, ffT, ⟨f⟩⟩ :=
    Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq R (B none)
      (deg none) (fun p => by rw [hdeg none]; rfl)
  haveI := fin₁; haveI := et₁; haveI := ff₁; haveI := ffT; haveI := finT; haveI := etT
  refine ⟨R₁ ⊗[R] T, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact Algebra.Etale.comp R R₁ (R₁ ⊗[R] T)
  · exact Module.FaithfullyFlat.trans R R₁ (R₁ ⊗[R] T)
  · rintro (_ | a)
    · exact nonempty_algEquiv_pi_of_algHom (B none) Algebra.TensorProduct.includeRight f
    · exact nonempty_algEquiv_pi_of_algHom (B (some a)) Algebra.TensorProduct.includeLeft (hs₁ a).some

end CSplitAux

theorem solution
    (R : Type u) [CommRing R]
    {ι : Type} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Finite R (B i)] [∀ i, Algebra.Etale R (B i)]
    (deg : ι → ℕ) (hdeg : ∀ i, Module.rankAtStalk (R := R) (B i) = deg i) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
      Module.Finite R R' ∧ Algebra.Etale R R' ∧ Module.FaithfullyFlat R R' ∧
      ∀ i, Nonempty (R' ⊗[R] (B i) ≃ₐ[R'] (Fin (deg i) → R')) :=
  (Finite.induction_empty_option (P := CSplitAux.P.{u}) (fun e h => CSplitAux.P_of_equiv e h)
    CSplitAux.P_empty (fun h => CSplitAux.P_option h) ι) R B deg hdeg

end S_Algebra_Etale_exists_faithfullyFlat_forall_nonempty_algEquiv_pi
end P2MW
export P2MW.S_Algebra_Etale_exists_faithfullyFlat_forall_nonempty_algEquiv_pi (solution)
