-- Prove2me | solution 1 for AlgebraicGeometry.isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/82f1427f-308d-5cd6-9ebb-a832f9987831

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SepGlue21

variable {S Y' : Scheme.{u}} (f' : Y' ⟶ S)

noncomputable abbrev δ {P Q : Scheme.{u}} (jP : P ⟶ Y') (jQ : Q ⟶ Y') :
    pullback jP jQ ⟶ pullback (jP ≫ f') (jQ ≫ f') :=
  pullback.map jP jQ (jP ≫ f') (jQ ≫ f') (𝟙 P) (𝟙 Q) f' (Category.id_comp _).symm (Category.id_comp _).symm

theorem isClosedImmersion_δ_self {P : Scheme.{u}} (j : P ⟶ Y') [Mono j]
    [IsClosedImmersion (pullback.diagonal (j ≫ f'))] : IsClosedImmersion (δ f' j j) := by
  haveI : IsIso (pullback.diagonal j) := inferInstance
  have h : δ f' j j = inv (pullback.diagonal j) ≫ pullback.diagonal (j ≫ f') := by
    rw [IsIso.eq_inv_comp]
    apply pullback.hom_ext
    · simp only [δ, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, pullback.diagonal_fst_assoc,
        Category.comp_id]
    · simp only [δ, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, pullback.diagonal_snd_assoc,
        Category.comp_id]
  rw [h]; infer_instance

theorem isClosedImmersion_δ_of_isPullback {A B U : Scheme.{u}} (jA : A ⟶ Y') (jB : B ⟶ Y')
    (uA : U ⟶ A) (uB : U ⟶ B) (hsq : IsPullback uA uB jA jB)
    (hΓ : IsClosedImmersion (pullback.lift uA uB
      (by rw [← Category.assoc, hsq.w, Category.assoc]) : U ⟶ pullback (jA ≫ f') (jB ≫ f'))) :
    IsClosedImmersion (δ f' jA jB) := by
  have h1 : hsq.isoPullback.hom ≫ δ f' jA jB =
      pullback.lift uA uB (by rw [← Category.assoc, hsq.w, Category.assoc]) := by
    apply pullback.hom_ext
    · simp only [δ, Category.assoc, pullback.lift_fst, Category.comp_id, IsPullback.isoPullback_hom_fst]
    · simp only [δ, Category.assoc, pullback.lift_snd, Category.comp_id, IsPullback.isoPullback_hom_snd]
  have h2 : δ f' jA jB = hsq.isoPullback.inv ≫
      pullback.lift uA uB (by rw [← Category.assoc, hsq.w, Category.assoc]) := by
    rw [← h1, Iso.inv_hom_id_assoc]
  rw [h2]; infer_instance

theorem isClosedImmersion_δ_symm {A B : Scheme.{u}} (jA : A ⟶ Y') (jB : B ⟶ Y')
    [IsClosedImmersion (δ f' jA jB)] : IsClosedImmersion (δ f' jB jA) := by
  have h : δ f' jB jA = (pullbackSymmetry jB jA).hom ≫ δ f' jA jB ≫ (pullbackSymmetry (jA ≫ f') (jB ≫ f')).hom := by
    apply pullback.hom_ext
    · simp only [δ, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id,
        pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_snd_assoc]
    · simp only [δ, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id,
        pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst_assoc]
  rw [h]; infer_instance

end SepGlue21

open SepGlue21 in
theorem solution
    {S Y' A B U : Scheme.{u}} (f' : Y' ⟶ S)
    (jA : A ⟶ Y') (jB : B ⟶ Y') [IsOpenImmersion jA] [IsOpenImmersion jB]
    (hcov : Set.range jA.base ∪ Set.range jB.base = Set.univ)
    (fA : A ⟶ S) (fB : B ⟶ S) (hA : jA ≫ f' = fA) (hB : jB ≫ f' = fB) [IsSeparated fA] [IsSeparated fB]
    (uA : U ⟶ A) (uB : U ⟶ B) (hsq : IsPullback uA uB jA jB)
    (hΓ : IsClosedImmersion
      (pullback.lift uA uB (by rw [← hA, ← hB, ← Category.assoc, hsq.w, Category.assoc]) : U ⟶ pullback fA fB)) :
    IsSeparated f' := by
  classical
  subst hA hB

  let XU : Bool → Scheme.{u} := fun b => cond b A B
  let fU : ∀ b : Bool, XU b ⟶ Y' := fun b => match b with
    | true => jA
    | false => jB
  have hfU : ∀ b : Bool, IsOpenImmersion (fU b) := by
    intro b; cases b
    · show IsOpenImmersion jB; infer_instance
    · show IsOpenImmersion jA; infer_instance
  let 𝒰 : Y'.OpenCover := ⟨⟨Bool, XU, fU⟩, ⟨by
      simpa using show ∀ y : Y', ∃ (b : Bool) (x : XU b), (fU b).base x = y from fun y => by
        have hy : y ∈ Set.range jA.base ∪ Set.range jB.base := by rw [hcov]; trivial
        rcases hy with ⟨x, hx⟩ | ⟨x, hx⟩
        · exact ⟨true, x, hx⟩
        · exact ⟨false, x, hx⟩, by simpa using hfU⟩⟩

  have hδ : ∀ a b : Bool, IsClosedImmersion (δ f' (𝒰.f a) (𝒰.f b)) := by
    intro a b
    cases a <;> cases b
    · show IsClosedImmersion (δ f' jB jB); exact isClosedImmersion_δ_self f' jB
    · show IsClosedImmersion (δ f' jB jA)
      haveI := isClosedImmersion_δ_of_isPullback f' jA jB uA uB hsq hΓ
      exact isClosedImmersion_δ_symm f' jA jB
    · show IsClosedImmersion (δ f' jA jB); exact isClosedImmersion_δ_of_isPullback f' jA jB uA uB hsq hΓ
    · show IsClosedImmersion (δ f' jA jA); exact isClosedImmersion_δ_self f' jA

  constructor
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 f' f')
  rintro ⟨a, b⟩
  have hP := pullback_map_diagonal_isPullback (𝒰.f a) (𝒰.f b) f'

  have e : hP.isoPullback.hom ≫ pullback.snd _ _ = δ f' (𝒰.f a) (𝒰.f b) := hP.isoPullback_hom_snd
  have h3 : IsClosedImmersion (hP.isoPullback.hom ≫ pullback.snd _ _) := by rw [e]; exact hδ a b
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion hP.isoPullback.hom _).mp h3

end S_AlgebraicGeometry_isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift
end P2MW
export P2MW.S_AlgebraicGeometry_isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift (solution)
