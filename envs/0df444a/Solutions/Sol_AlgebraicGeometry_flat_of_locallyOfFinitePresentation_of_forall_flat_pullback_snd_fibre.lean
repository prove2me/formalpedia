-- Prove2me | solution 1 for AlgebraicGeometry.flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9571e14a-ab87-5979-80cd-cf189fab6187

import Mathlib
import Theorems.Thm_Module_Flat_of_finitePresentation_of_forall_flat_residueField_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre.AlgebraicGeometry TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp pullbackSpecIso_inv_snd pullbackSpecIso_inv_fst' IsZariskiLocalAtSource.iff_of_openCover Flat.SpecMap_iff Scheme.Spec.residueFieldIso IsZariskiLocalAtTarget Spec Spec.map Scheme pullbackSpecIso Spec.map_surjective IsZariskiLocalAtSource IsOpenImmersion Scheme.Cover.pullbackHom Flat IsZariskiLocalAtTarget.iff_of_openCover HasRingHomProperty.Spec_iff Spec.map_id Scheme.Spec Flat.comp locallyOfFinitePresentation_of_isOpenImmersion LocallyOfFinitePresentation Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField HasRingHomProperty Scheme.Cover"
namespace FlatFibreCriterionTwoScheme
p2m_open "AlgebraicGeometry"

lemma flat_snd_comp {X Y Z Z' : Scheme.{u}} (g : X ⟶ Y) (a : Z ⟶ Y) (ψ : Z' ⟶ Z)
    [Flat (pullback.snd g a)] : Flat (pullback.snd g (ψ ≫ a)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd g a ψ]
  infer_instance

lemma flat_snd_snd {X Y Y' Z : Scheme.{u}} (g : X ⟶ Y) (c : Y' ⟶ Y) (b : Z ⟶ Y')
    [Flat (pullback.snd g (b ≫ c))] : Flat (pullback.snd (pullback.snd g c) b) := by
  rw [← pullbackLeftPullbackSndIso_hom_snd g c b]
  infer_instance

lemma flat_snd_comp_left {X X' Y Z : Scheme.{u}} (g : X ⟶ Y) (i : X' ⟶ X) [Flat i]
    (a : Z ⟶ Y) [Flat (pullback.snd g a)] : Flat (pullback.snd (i ≫ g) a) := by
  rw [(Iso.eq_inv_comp _).mpr (pullbackRightPullbackFstIso_hom_snd g a i)]
  infer_instance

lemma flat_of_isOpenImmersion {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] : Flat i :=
  inferInstance

def FibrewiseFlat {S X Y : Scheme.{u}} (g : X ⟶ Y) (pY : Y ⟶ S) : Prop :=
  ∀ s : S, Flat (pullback.snd g (pullback.fst pY (S.fromSpecResidueField s)))

lemma map_id_toAlgHom_toRingHom_eq {R A B K : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing K] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [Algebra R K] :
    (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R A B)).toRingHom =
      ((Algebra.TensorProduct.comm R B K).toRingHom.comp
        (Algebra.TensorProduct.cancelBaseChange R A A B K).toRingHom).comp
      ((Algebra.TensorProduct.includeRight :
          A ⊗[R] K →ₐ[A] B ⊗[A] (A ⊗[R] K)).toRingHom.comp
        (Algebra.TensorProduct.comm R K A).toRingHom) := by
  refine RingHom.ext fun x ↦ ?_
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul k a =>
      simp [Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma flat_map_of_flat_pullback_snd {R A B K : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing K] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [Algebra R K]
    [Flat (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] K)))))] :
    (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R A B)).toRingHom.Flat := by
  have h3 : Flat ((pullbackSpecIso A B (A ⊗[R] K)).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] K))))) := inferInstance
  rw [pullbackSpecIso_inv_snd, Flat.SpecMap_iff, CommRingCat.hom_ofHom] at h3
  rw [map_id_toAlgHom_toRingHom_eq]
  refine RingHom.Flat.comp (RingHom.Flat.comp ?_ h3) (RingHom.Flat.comp ?_ ?_)
  · exact RingHom.Flat.of_bijective (f := (Algebra.TensorProduct.comm R K A).toRingHom)
      (Algebra.TensorProduct.comm R K A).bijective
  · exact RingHom.Flat.of_bijective
      (f := (Algebra.TensorProduct.cancelBaseChange R A A B K).toRingHom)
      (Algebra.TensorProduct.cancelBaseChange R A A B K).bijective
  · exact RingHom.Flat.of_bijective (f := (Algebra.TensorProduct.comm R B K).toRingHom)
      (Algebra.TensorProduct.comm R B K).bijective

theorem flat_SpecMap_of_forall_flat_pullback_snd_fibre
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (hfpB : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (hfpA : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (hfib : ∀ s : Spec (.of R), Flat (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        ((Spec (.of R)).fromSpecResidueField s)))) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff] at hflat ⊢
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation), CommRingCat.hom_ofHom,
    RingHom.finitePresentation_algebraMap] at hfpA hfpB
  refine Module.Flat.of_finitePresentation_of_forall_flat_residueField_tensorProduct
    (R := R) (A := A) (B := B) fun p _ ↦ ?_

  let K := p.ResidueField
  let s : Spec (.of R) := ⟨p, ‹_›⟩
  let pA := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))

  let ιK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hι : ιK ≫ 𝟙 (Spec (.of R)) =
      Spec.map (Scheme.Spec.residueFieldIso (.of R) s).hom ≫ (Spec (.of R)).fromSpecResidueField s := by
    rw [Category.comp_id, ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
  let ψ₁ := pullback.map pA ιK pA ((Spec (.of R)).fromSpecResidueField s) (𝟙 _)
    (Spec.map (Scheme.Spec.residueFieldIso (.of R) s).hom) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp]) hι
  have e₁ : ψ₁ ≫ pullback.fst pA ((Spec (.of R)).fromSpecResidueField s) = pullback.fst pA ιK := by
    simp only [ψ₁, pullback.lift_fst, Category.comp_id]
  haveI := hfib s
  haveI : Flat (pullback.snd g (pullback.fst pA ιK)) := by
    rw [← e₁]; exact flat_snd_comp g _ ψ₁

  have e₂ : (pullbackSpecIso R A K).inv ≫ pullback.fst pA ιK =
      Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] K))) :=
    pullbackSpecIso_inv_fst' R A K
  haveI : Flat (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] K))))) := by
    rw [← e₂]; exact flat_snd_comp g _ _

  exact flat_map_of_flat_pullback_snd (R := R) (A := A) (B := B) (K := K)

theorem flat_of_forall_flat_pullback_snd_fibre
    {S X Y : Scheme.{u}} (g : X ⟶ Y) (pY : Y ⟶ S)
    [Flat (g ≫ pY)] [LocallyOfFinitePresentation (g ≫ pY)] [LocallyOfFinitePresentation pY]
    (hfib : FibrewiseFlat g pY) :
    Flat g := by

  wlog hS : ∃ R, S = Spec R generalizing S X Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) (S.affineCover.pullback₁ pY)]
    intro i
    dsimp [Scheme.Cover.pullbackHom]

    have hpb : IsPullback (pullback.fst g (pullback.fst pY (S.affineCover.f i)))
        (pullback.snd g (pullback.fst pY (S.affineCover.f i)) ≫
          pullback.snd pY (S.affineCover.f i)) (g ≫ pY) (S.affineCover.f i) :=
      (IsPullback.of_hasPullback g _).paste_vert
        (IsPullback.of_hasPullback pY (S.affineCover.f i))
    have hF : Flat (pullback.snd g (pullback.fst pY (S.affineCover.f i)) ≫
        pullback.snd pY (S.affineCover.f i)) :=
      MorphismProperty.of_isPullback (P := @Flat) hpb ‹_›
    have hL : LocallyOfFinitePresentation (pullback.snd g (pullback.fst pY (S.affineCover.f i)) ≫
        pullback.snd pY (S.affineCover.f i)) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb ‹_›
    have hL' : LocallyOfFinitePresentation (pullback.snd pY (S.affineCover.f i)) :=
      MorphismProperty.pullback_snd _ _ ‹_›
    refine this (pullback.snd g (pullback.fst pY (S.affineCover.f i)))
      (pullback.snd pY (S.affineCover.f i)) (fun s' ↦ ?_) ⟨_, rfl⟩

    have e : pullback.fst (pullback.snd pY (S.affineCover.f i))
          ((S.affineCover.X i).fromSpecResidueField s') ≫ pullback.fst pY (S.affineCover.f i) =
        pullback.map (pullback.snd pY (S.affineCover.f i))
          ((S.affineCover.X i).fromSpecResidueField s')
          pY (S.fromSpecResidueField ((S.affineCover.f i) s'))
          (pullback.fst pY (S.affineCover.f i))
          (Spec.map ((S.affineCover.f i).residueFieldMap s'))
          (S.affineCover.f i) pullback.condition.symm
          ((S.affineCover.f i).SpecMap_residueFieldMap_fromSpecResidueField s').symm ≫
        pullback.fst pY (S.fromSpecResidueField ((S.affineCover.f i) s')) :=
      (pullback.lift_fst _ _ _).symm
    have h1 := hfib ((S.affineCover.f i) s')
    have h2 : Flat (pullback.snd g (pullback.fst (pullback.snd pY (S.affineCover.f i))
        ((S.affineCover.X i).fromSpecResidueField s') ≫ pullback.fst pY (S.affineCover.f i))) := by
      rw [e]; exact flat_snd_comp g _ _
    exact flat_snd_snd g _ _
  obtain ⟨R, rfl⟩ := hS

  wlog hY : ∃ A, Y = Spec A generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) Y.affineCover]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    have heq : pullback.snd g (Y.affineCover.f i) ≫ (Y.affineCover.f i ≫ pY) =
        pullback.fst g (Y.affineCover.f i) ≫ (g ≫ pY) := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
    have hF : Flat (pullback.snd g (Y.affineCover.f i) ≫ (Y.affineCover.f i ≫ pY)) := by
      rw [heq]
      exact MorphismProperty.comp_mem @Flat _ _
        (MorphismProperty.pullback_fst _ _ (flat_of_isOpenImmersion _)) ‹_›
    have hL : LocallyOfFinitePresentation
        (pullback.snd g (Y.affineCover.f i) ≫ (Y.affineCover.f i ≫ pY)) := by
      rw [heq]
      exact MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _
        (MorphismProperty.pullback_fst _ _ (locallyOfFinitePresentation_of_isOpenImmersion _)) ‹_›
    have hL' : LocallyOfFinitePresentation (Y.affineCover.f i ≫ pY) :=
      MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _
        (locallyOfFinitePresentation_of_isOpenImmersion _) ‹_›
    refine this (pullback.snd g (Y.affineCover.f i)) (Y.affineCover.f i ≫ pY)
      (fun s ↦ ?_) ⟨_, rfl⟩
    have e : pullback.fst (Y.affineCover.f i ≫ pY) ((Spec R).fromSpecResidueField s) ≫
          Y.affineCover.f i =
        pullback.map (Y.affineCover.f i ≫ pY) ((Spec R).fromSpecResidueField s) pY
          ((Spec R).fromSpecResidueField s) (Y.affineCover.f i) (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]) ≫
        pullback.fst pY ((Spec R).fromSpecResidueField s) :=
      (pullback.lift_fst _ _ _).symm
    have h1 := hfib s
    have h2 : Flat (pullback.snd g
        (pullback.fst (Y.affineCover.f i ≫ pY) ((Spec R).fromSpecResidueField s) ≫
          Y.affineCover.f i)) := by
      rw [e]; exact flat_snd_comp g _ _
    exact flat_snd_snd g _ _
  obtain ⟨A, rfl⟩ := hY

  wlog hX : ∃ B, X = Spec B generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Flat) X.affineCover]
    intro i
    have hF : Flat ((X.affineCover.f i ≫ g) ≫ pY) := by
      rw [Category.assoc]
      exact MorphismProperty.comp_mem @Flat _ _ (flat_of_isOpenImmersion _) ‹_›
    have hL : LocallyOfFinitePresentation ((X.affineCover.f i ≫ g) ≫ pY) := by
      rw [Category.assoc]
      exact MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _
        (locallyOfFinitePresentation_of_isOpenImmersion _) ‹_›
    have hO : Flat (X.affineCover.f i) := flat_of_isOpenImmersion _
    refine this (X.affineCover.f i ≫ g) (fun s ↦ ?_) ⟨_, rfl⟩
    have h1 := hfib s
    exact flat_snd_comp_left g (X.affineCover.f i) _
  obtain ⟨B, rfl⟩ := hX

  obtain ⟨φY, rfl⟩ := Spec.map_surjective pY
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  algebraize [φY.hom, φ.hom]
  letI : Algebra R B := (φ.hom.comp φY.hom).toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have e : Spec.map φ ≫ Spec.map φY = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [← Spec.map_comp]; rfl
  have h1 : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) := e ▸ ‹_›
  have h2 : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R B))) := e ▸ ‹_›
  exact flat_SpecMap_of_forall_flat_pullback_snd_fibre (R := R) (A := A) (B := B) h1 h2 ‹_› hfib

end AlgebraicGeometry.FlatFibreCriterionTwoScheme

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre.AlgebraicGeometry in
open AlgebraicGeometry.FlatFibreCriterionTwoScheme in
theorem solution
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (g : X ⟶ Y) (hg : g ≫ pY = pX)
    [Flat pX] [LocallyOfFinitePresentation pX] [LocallyOfFinitePresentation pY]
    (hfib : ∀ s : S, Flat (pullback.snd g (pY.fiberι s))) :
    Flat g := by
  have hF : Flat (g ≫ pY) := by rw [hg]; infer_instance
  have hL : LocallyOfFinitePresentation (g ≫ pY) := by rw [hg]; infer_instance
  exact flat_of_forall_flat_pullback_snd_fibre g pY fun s ↦ hfib s

end S_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre
end P2MW
export P2MW.S_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre (solution)
