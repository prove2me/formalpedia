-- Prove2me | solution 1 for AlgebraicGeometry.universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/866a99b0-d78a-5b5f-a862-40e07327761d

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace UCAffineGC4

theorem coe_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) : ⇑(a ≫ b).base = ⇑b.base ∘ ⇑a.base :=
  funext fun x => Scheme.Hom.comp_apply a b x

theorem isClosedMap_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (ha : IsClosedMap a.base) (hb : IsClosedMap b.base) : IsClosedMap (a ≫ b).base := by
  rw [coe_comp]; exact hb.comp ha

theorem isClosedMap_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] : IsClosedMap e.base :=
  (Scheme.homeoOfIso (asIso e)).isClosedMap

theorem surjective_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] : Function.Surjective e.base :=
  (Scheme.homeoOfIso (asIso e)).surjective

theorem isClosedMap_of_iso_comp {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (b : Y ⟶ Z)
    (h : IsClosedMap (e ≫ b).base) : IsClosedMap b.base := by
  rw [coe_comp] at h
  exact IsClosedMap.of_comp_surjective (surjective_of_isIso e) e.base.hom.continuous h

theorem isClosedMap_of_comp_closedImmersion {X Y Z : Scheme.{u}} (a : X ⟶ Y) (c : Y ⟶ Z) [IsClosedImmersion c]
    (h : IsClosedMap (a ≫ c).base) : IsClosedMap a.base := by
  intro S hS
  have h1 := h S hS
  rw [coe_comp, Set.image_comp] at h1
  rw [← c.isClosedEmbedding.injective.preimage_image (a.base '' S)]
  exact h1.preimage c.base.hom.continuous

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

theorem isClosedMap_of_surjective {T T' : Type u} [CommRing T] [CommRing T'] [Algebra R T] [Algebra R T']
    (ψ : T' →ₐ[R] T) (hψ : Function.Surjective ψ)
    (hT' : IsClosedMap (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R T')))).base) :
    IsClosedMap (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R T)))).base := by
  let c : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of T') := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  haveI : IsClosedImmersion c := IsClosedImmersion.spec_of_surjective _ hψ
  have hc : c ≫ Spec.map (CommRingCat.ofHom (algebraMap R T')) = Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => ψ.commutes r
  let gT' := Spec.map (CommRingCat.ofHom (algebraMap R T'))

  have hQ : IsClosedMap (pullback.snd (pullback.snd f gT') c).base := by
    apply isClosedMap_of_comp_closedImmersion _ c
    rw [← pullback.condition]
    exact isClosedMap_comp _ _ (pullback.fst (pullback.snd f gT') c).isClosedEmbedding.isClosedMap hT'
  let E : pullback (pullback.snd f gT') c ≅ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R T))) :=
    pullbackLeftPullbackSndIso f gT' c ≪≫ pullback.congrHom rfl hc
  have hE : E.hom ≫ pullback.snd f _ = pullback.snd (pullback.snd f gT') c := by
    simp only [E, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
    exact pullbackLeftPullbackSndIso_hom_snd _ _ _
  apply isClosedMap_of_iso_comp E.hom
  rw [hE]; exact hQ

theorem isClosedMap_of_algebra [QuasiCompact f]
    (H : ∀ (ι : Type u) [Finite ι], IsClosedMap
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))))).base)
    (A : Type u) [CommRing A] [Algebra R A] :
    IsClosedMap (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).base := by
  classical
  let S : Finset A → Subalgebra R A := fun F => Algebra.adjoin R (F : Set A)
  have hdir : Directed (· ≤ ·) S := fun F G =>
    ⟨F ∪ G, Algebra.adjoin_mono (by simp [Finset.coe_union]), Algebra.adjoin_mono (by simp [Finset.coe_union])⟩
  have hS : ∀ a : A, ∃ F, a ∈ S F := fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩
  let q : ∀ F, pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥(S F)))) := fun F =>
    pullback.lift (pullback.fst f _) (pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(S F) A)))
      (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq])
  refine AlgebraicGeometry.isClosedMap_pullback_snd_of_directed_subalgebra S hdir hS f q
    (fun F => pullback.lift_fst _ _ _) (fun F => pullback.lift_snd _ _ _) fun F => ?_

  haveI : Finite ↥((F : Finset A) : Set A) := F.finite_toSet.to_subtype
  let ψ : MvPolynomial ↥((F : Finset A) : Set A) R →ₐ[R] A := MvPolynomial.aeval Subtype.val
  have hrange : S F = ψ.range := Algebra.adjoin_eq_range R _
  let ψ' : MvPolynomial ↥((F : Finset A) : Set A) R →ₐ[R] ↥(S F) :=
    (Subalgebra.equivOfEq _ _ hrange.symm).toAlgHom.comp ψ.rangeRestrict
  have hψ' : Function.Surjective ψ' :=
    (Subalgebra.equivOfEq _ _ hrange.symm).surjective.comp ψ.rangeRestrict_surjective
  exact isClosedMap_of_surjective f ψ' hψ' (H _)

theorem isClosedMap_of_isAffine [QuasiCompact f]
    (H : ∀ (ι : Type u) [Finite ι], IsClosedMap
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))))).base)
    (T : Scheme.{u}) [IsAffine T] (t : T ⟶ Spec (CommRingCat.of R)) :
    IsClosedMap (pullback.snd f t).base := by
  let φ := Spec.preimage (T.isoSpec.inv ≫ t)
  letI : Algebra R Γ(T, ⊤) := φ.hom.toAlgebra
  have e : T.isoSpec.inv ≫ t = Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, ⊤))) := by
    have : CommRingCat.ofHom (algebraMap R Γ(T, ⊤)) = φ := rfl
    rw [this, Spec.map_preimage]
  have h0 := isClosedMap_of_algebra f H Γ(T, ⊤)
  have h1 : IsClosedMap (pullback.snd f (T.isoSpec.inv ≫ t)).base := by
    apply isClosedMap_of_iso_comp (pullback.congrHom rfl e).inv
    have : (pullback.congrHom (rfl : f = f) e).inv ≫ pullback.snd f (T.isoSpec.inv ≫ t) = pullback.snd f _ := by
      simp only [pullback.congrHom_inv, pullback.lift_snd, Category.comp_id]
    rw [this]
    exact h0
  let m := pullback.map f (T.isoSpec.inv ≫ t) f t (𝟙 X) T.isoSpec.inv (𝟙 _) (by simp) (by simp)
  have hm : m ≫ pullback.snd f t = pullback.snd f _ ≫ T.isoSpec.inv := pullback.lift_snd _ _ _
  apply isClosedMap_of_iso_comp m
  rw [hm]
  exact isClosedMap_comp _ _ h1 (isClosedMap_of_isIso _)

theorem isClosedMap_pullback_snd [QuasiCompact f]
    (H : ∀ (ι : Type u) [Finite ι], IsClosedMap
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))))).base)
    (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)) :
    IsClosedMap (pullback.snd f t).base := by
  have hcov : TopologicalSpace.IsOpenCover (fun V : T.affineOpens => (V : T.Opens)) := iSup_affineOpens_eq_top T
  rw [hcov.isClosedMap_iff_restrictPreimage]
  intro V
  haveI : IsAffine (V : T.Opens) := V.2
  have h := isClosedMap_of_isAffine f H (V : T.Opens) ((V : T.Opens).ι ≫ t)
  have h2 : IsClosedMap (pullback.snd (pullback.snd f t) (V : T.Opens).ι).base := by
    rw [← pullbackLeftPullbackSndIso_hom_snd f t (V : T.Opens).ι]
    exact isClosedMap_comp _ _ (isClosedMap_of_isIso _) h
  have h3 : IsClosedMap (pullback.snd f t ∣_ (V : T.Opens)).base := by
    delta morphismRestrict
    exact isClosedMap_comp _ _ (isClosedMap_of_isIso _) h2
  rwa [morphismRestrict_base] at h3

end UCAffineGC4

open UCAffineGC4 in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (H : ∀ (ι : Type u) [Finite ι], IsClosedMap
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))))).base) :
    UniversallyClosed f := by
  haveI : (topologically @IsClosedMap).RespectsIso :=
    topologically_respectsIso _ (fun e => e.isClosedMap) (fun _ _ hf hg => hg.comp hf)
  rw [universallyClosed_iff]
  apply MorphismProperty.universally_mk'
  intro T t _
  show IsClosedMap (pullback.fst t f).base
  rw [← pullbackSymmetry_hom_comp_snd]
  exact isClosedMap_comp _ _ (isClosedMap_of_isIso _) (isClosedMap_pullback_snd f H T t)

end S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial
end P2MW
export P2MW.S_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial (solution)
