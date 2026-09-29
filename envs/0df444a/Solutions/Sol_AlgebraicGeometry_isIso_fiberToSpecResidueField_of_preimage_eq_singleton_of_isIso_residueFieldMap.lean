-- Prove2me | solution 1 for AlgebraicGeometry.isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/01cb54f8-6027-5196-a4ce-c4fc88d1062d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap.AlgebraicGeometry"

namespace Algebra
p2m_export "Algebra" "EssFiniteType FormallyUnramified.map_maximalIdeal algebraMap FormallyUnramified map_bot FiniteType"
namespace FormallyUnramified
p2m_export "Algebra.FormallyUnramified" "map_maximalIdeal ext comp"
p2m_open "Algebra.FormallyUnramified Algebra"

theorem isLocalHom_algebraMap_of_field (K A : Type*) [Field K] [CommRing A] [IsLocalRing A] [Algebra K A] :
    IsLocalHom (algebraMap K A) := by
  refine ⟨fun a ha => ?_⟩
  rcases eq_or_ne a 0 with rfl | h
  · rw [map_zero] at ha
    exact (not_isUnit_zero ha).elim
  · exact isUnit_iff_ne_zero.mpr h

theorem isField_of_isLocalRing_of_field {K A : Type*} [Field K] [CommRing A] [IsLocalRing A] [Algebra K A]
    [Algebra.EssFiniteType K A] [Algebra.FormallyUnramified K A] : IsField A := by
  haveI := isLocalHom_algebraMap_of_field K A
  have h := Algebra.FormallyUnramified.map_maximalIdeal (R := K) (S := A)
  rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp (Field.toIsField K), Ideal.map_bot] at h
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr h.symm

theorem bijective_algebraMap_of_surjective_residue {K A : Type*} [Field K] [CommRing A] [IsLocalRing A] [Algebra K A]
    [Algebra.EssFiniteType K A] [Algebra.FormallyUnramified K A]
    (h : Function.Surjective ((IsLocalRing.residue A).comp (algebraMap K A))) :
    Function.Bijective (algebraMap K A) := by
  have hF := isField_of_isLocalRing_of_field (K := K) (A := A)
  have hbot : IsLocalRing.maximalIdeal A = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
  have hinj : Function.Injective (IsLocalRing.residue A) := by
    rw [RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue, hbot]
  refine ⟨(algebraMap K A).injective, fun a => ?_⟩
  obtain ⟨k, hk⟩ := h (IsLocalRing.residue A a)
  exact ⟨k, hinj hk⟩

end Algebra.FormallyUnramified

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "HasRingHomProperty.iff_of_isAffine Surjective Scheme.residueFieldMap_comp Scheme.Hom Scheme.Hom.range_fiberι Surjective.of_comp IsAffine.of_isIso stalkClosedPointIso IsAffine Scheme.Γevaluation_naturality Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme ΓSpecIso_hom_stalkClosedPointIso_inv Scheme.Hom.fiberι_asFiber Scheme.isoSpec_hom_naturality Scheme.residue_residueFieldMap FormallyUnramified HasRingHomProperty Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

theorem isIso_of_isAffine_of_bijective_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (φ : X ⟶ Y)
    (h : Function.Bijective φ.appTop.hom) : IsIso φ := by
  have e : φ = X.isoSpec.hom ≫ Spec.map φ.appTop ≫ Y.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI : IsIso φ.appTop := by
    have : IsIso ((forget CommRingCat).map φ.appTop) := (isIso_iff_bijective _).mpr h
    exact isIso_of_reflects_iso φ.appTop (forget CommRingCat)
  rw [e]
  infer_instance

theorem isIso_of_isAffine_of_bijective_ΓSpecIso_inv_appTop {X : Scheme.{u}} [IsAffine X] {K : CommRingCat.{u}}
    (φ : X ⟶ Spec K) (h : Function.Bijective ((Scheme.ΓSpecIso K).inv ≫ φ.appTop).hom) : IsIso φ := by
  apply isIso_of_isAffine_of_bijective_appTop
  have hb : Function.Bijective (Scheme.ΓSpecIso K).hom.hom := (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.bijective
  have : φ.appTop.hom = ((Scheme.ΓSpecIso K).inv ≫ φ.appTop).hom.comp (Scheme.ΓSpecIso K).hom.hom := by
    rw [← CommRingCat.hom_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [this, RingHom.coe_comp]
  exact h.comp hb

end AlgebraicGeometry

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "HasRingHomProperty.iff_of_isAffine Surjective Scheme.residueFieldMap_comp Scheme.Hom Scheme.Hom.range_fiberι Surjective.of_comp IsAffine.of_isIso stalkClosedPointIso IsAffine Scheme.Γevaluation_naturality Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme ΓSpecIso_hom_stalkClosedPointIso_inv Scheme.Hom.fiberι_asFiber Scheme.isoSpec_hom_naturality Scheme.residue_residueFieldMap FormallyUnramified HasRingHomProperty Scheme.ΓSpecIso"
namespace Layer0
namespace W6
p2m_open "AlgebraicGeometry"

theorem surjective_residueFieldMap_of_surjective_stalkMap {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    (h : Function.Surjective (g.stalkMap x)) : Function.Surjective (g.residueFieldMap x) := by
  have hc : Function.Surjective (g.stalkMap x ≫ X.residue x) := by
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (X.residue_surjective x).comp h
  rw [← Scheme.residue_residueFieldMap] at hc
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hc
  exact Function.Surjective.of_comp hc

theorem surjective_Γevaluation_Spec_field (K : Type u) [Field K] (p : ↥(Spec (CommRingCat.of K))) :
    Function.Surjective ((Spec (CommRingCat.of K)).Γevaluation p) := by
  have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  subst hp
  change Function.Surjective ((Spec (CommRingCat.of K)).presheaf.germ ⊤ (IsLocalRing.closedPoint K) trivial ≫
    (Spec (CommRingCat.of K)).residue _)
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  refine ((Spec (CommRingCat.of K)).residue_surjective _).comp ?_
  exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of K)).inv).2.comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).hom).2

theorem _root_.P2MW.S_AlgebraicGeometry_isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap.solution
    {U S : Scheme.{u}} (f : U ⟶ S)
    [LocallyOfFiniteType f] [FormallyUnramified f]
    (x : U) (hx : ∀ y : U, f y = f x → y = x) [IsIso (f.residueFieldMap x)] :
    IsIso (f.fiberToSpecResidueField (f x)) := by

  haveI : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  haveI : FormallyUnramified (f.fiberToSpecResidueField (f x)) :=
    MorphismProperty.pullback_snd (P := @FormallyUnramified) _ _ inferInstance
  set K := S.residueField (f x) with hK
  set φ := f.fiberToSpecResidueField (f x) with hφ
  set z₀ : ↥(f.fiber (f x)) := f.asFiber x with hz₀

  have hpt : ∀ z : ↥(f.fiber (f x)), z = z₀ := by
    intro z
    apply (f.fiberι (f x)).isEmbedding.injective
    rw [hz₀, Scheme.Hom.fiberι_asFiber]
    apply hx
    have : f.fiberι (f x) z ∈ f ⁻¹' {f x} := by rw [← Scheme.Hom.range_fiberι]; exact Set.mem_range_self z
    simpa using this

  haveI : IsAffine (f.fiber (f x)) := by
    obtain ⟨V, hV, hzV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp (f.fiber (f x)).isBasis_affineOpens
      (show z₀ ∈ (⊤ : (f.fiber (f x)).Opens) from trivial)
    have hVtop : V = ⊤ := by
      ext z; exact ⟨fun _ => trivial, fun _ => (hpt z).symm ▸ hzV⟩
    subst hVtop
    haveI : IsAffine (⊤ : (f.fiber (f x)).Opens) := hV
    exact IsAffine.of_isIso (f.fiber (f x)).topIso.inv

  have hS : Function.Surjective (φ.residueFieldMap z₀) := by
    have hA' : Function.Surjective (f.residueFieldMap (f.fiberι (f x) z₀)) := by
      rw [hz₀, Scheme.Hom.fiberι_asFiber]
      exact (ConcreteCategory.bijective_of_isIso (f.residueFieldMap x)).2
    have hB' : Function.Surjective ((f.fiberι (f x)).residueFieldMap z₀) :=
      surjective_residueFieldMap_of_surjective_stalkMap _ _ ((f.fiberι (f x)).stalkMap_surjective z₀)
    have h1 : Function.Surjective ((f.fiberι (f x) ≫ f).residueFieldMap z₀) := by
      rw [Scheme.residueFieldMap_comp]
      intro c
      obtain ⟨m, hm⟩ := hB' c
      obtain ⟨k, hk⟩ := hA' m
      exact ⟨k, show (f.fiberι (f x)).residueFieldMap z₀ (f.residueFieldMap (f.fiberι (f x) z₀) k) = c by rw [hk, hm]⟩
    have hcond : f.fiberι (f x) ≫ f = φ ≫ S.fromSpecResidueField (f x) := pullback.condition
    rw [hcond, Scheme.residueFieldMap_comp] at h1
    have h1' : Function.Surjective (⇑(φ.residueFieldMap z₀) ∘ ⇑((S.fromSpecResidueField (f x)).residueFieldMap (φ z₀))) :=
      fun c => by obtain ⟨k, hk⟩ := h1 c; exact ⟨k, hk⟩
    exact Function.Surjective.of_comp h1'

  set A := Γ(f.fiber (f x), ⊤) with hA
  let ι : (K : Type u) →+* (A : Type u) := ((Scheme.ΓSpecIso K).inv ≫ φ.appTop).hom
  have hft : ι.FiniteType := by
    change ((Scheme.ΓSpecIso K).inv ≫ φ.appTop).hom.FiniteType
    rw [CommRingCat.hom_comp, RingHom.finiteType_respectsIso.cancel_left_isIso (Scheme.ΓSpecIso K).inv φ.appTop]
    exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  have hfu : ι.FormallyUnramified := by
    change ((Scheme.ΓSpecIso K).inv ≫ φ.appTop).hom.FormallyUnramified
    rw [CommRingCat.hom_comp, RingHom.FormallyUnramified.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso K).inv φ.appTop]
    exact (HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified)).mp inferInstance
  letI : Algebra K A := ι.toAlgebra
  haveI : Algebra.FiniteType K A := hft
  haveI : Algebra.FormallyUnramified K A := hfu

  have hsubF : ∀ a b : ↥(f.fiber (f x)), a = b := fun a b => (hpt a).trans (hpt b).symm
  have hsubP : ∀ a b : PrimeSpectrum A, a = b := fun a b => by
    apply (Scheme.homeoOfIso (f.fiber (f x)).isoSpec).symm.injective
    exact hsubF _ _
  haveI : Nontrivial A := PrimeSpectrum.nontrivial ((Scheme.homeoOfIso (f.fiber (f x)).isoSpec) z₀)
  haveI : IsLocalRing A := by
    refine IsLocalRing.of_unique_max_ideal ?_
    obtain ⟨M, hM⟩ := Ideal.exists_maximal A
    exact ⟨M, hM, fun M' hM' => congrArg PrimeSpectrum.asIdeal (hsubP ⟨M', hM'.isPrime⟩ ⟨M, hM.isPrime⟩)⟩
  have hF : IsField A := Algebra.FormallyUnramified.isField_of_isLocalRing_of_field (K := K) (A := A)

  have hT : Function.Surjective (((f.fiber (f x)).Γevaluation z₀).hom.comp ι) := by
    have hnat := Scheme.Γevaluation_naturality φ z₀
    have heq : ((f.fiber (f x)).Γevaluation z₀).hom.comp ι =
        (φ.residueFieldMap z₀).hom.comp (((Spec K).Γevaluation (φ z₀)).hom.comp (Scheme.ΓSpecIso K).inv.hom) := by
      change ((f.fiber (f x)).Γevaluation z₀).hom.comp ((Scheme.ΓSpecIso K).inv ≫ φ.appTop).hom = _
      rw [← CommRingCat.hom_comp, Category.assoc, ← hnat]
      rfl
    rw [heq]
    simp only [RingHom.coe_comp]
    refine hS.comp (Function.Surjective.comp ?_ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso K).inv).2)
    exact surjective_Γevaluation_Spec_field _ _

  have hψinj : Function.Injective ((f.fiber (f x)).Γevaluation z₀).hom := by
    letI := hF.toField
    exact RingHom.injective _
  have hιbij : Function.Bijective ι := by
    refine ⟨ι.injective, fun a => ?_⟩
    obtain ⟨k, hk⟩ := hT (((f.fiber (f x)).Γevaluation z₀).hom a)
    exact ⟨k, hψinj hk⟩
  exact isIso_of_isAffine_of_bijective_ΓSpecIso_inv_appTop φ hιbij

end AlgebraicGeometry.Layer0.W6

end S_AlgebraicGeometry_isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap (solution)
