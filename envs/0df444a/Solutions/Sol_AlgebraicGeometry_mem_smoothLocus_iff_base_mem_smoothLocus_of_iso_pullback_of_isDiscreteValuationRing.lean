-- Prove2me | solution 1 for AlgebraicGeometry.mem_smoothLocus_iff_base_mem_smoothLocus_of_iso_pullback_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ab7db874-5400-5653-a3d0-06694aefb989

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicGeometry_mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_quotient_map_maximalIdeal_of_iso_pullback_of_residue_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_mem_smoothLocus_iff_base_mem_smoothLocus_of_iso_pullback_of_isDiscreteValuationRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TensorProduct

namespace BCSmoothAux

theorem formallySmooth_transport {k₀ k B₀ B : Type*} [CommRing k₀] [CommRing k] [CommRing B₀] [CommRing B]
    [Algebra k₀ B₀] [Algebra k B] (r : k₀ ≃+* k) (e : B₀ ≃+* B)
    (hcomm : ∀ a : k₀, e (algebraMap k₀ B₀ a) = algebraMap k B (r a))
    [Algebra.FormallySmooth k B] : Algebra.FormallySmooth k₀ B₀ := by
  letI algkk : Algebra k₀ k := r.toRingHom.toAlgebra
  letI algkB : Algebra k₀ B := ((algebraMap k B).comp r.toRingHom).toAlgebra
  haveI : IsScalarTower k₀ k B := IsScalarTower.of_algebraMap_eq' rfl

  let rₐ : k₀ ≃ₐ[k₀] k := AlgEquiv.ofRingEquiv (f := r) (fun a => rfl)
  haveI : Algebra.FormallySmooth k₀ k := Algebra.FormallySmooth.of_equiv rₐ
  haveI : Algebra.FormallySmooth k₀ B := Algebra.FormallySmooth.comp k₀ k B

  let eₐ : B₀ ≃ₐ[k₀] B := AlgEquiv.ofRingEquiv (f := e) (fun a => by
    rw [hcomm]; rfl)
  exact Algebra.FormallySmooth.of_equiv eₐ.symm

end BCSmoothAux

namespace BCSmoothAux

theorem const_eq_comp (A : Type) [CommRing A]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (x : X) :
    (X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) =
      (f.stalkMap x).hom.comp (StructureSheaf.toStalk A (f.base x)).hom := by
  have h1 : (Spec (CommRingCat.of A)).presheaf.germ ⊤ (f.base x) trivial ≫ f.stalkMap x =
      f.appTop ≫ X.presheaf.germ ⊤ x trivial :=
    Scheme.Hom.germ_stalkMap f ⊤ x trivial
  have h2 : (X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom := by
    simp only [CommRingCat.hom_comp, RingHom.comp_assoc]
  rw [h2, ← h1]
  rfl

theorem isLocalHom_const (A : Type) [CommRing A] [IsLocalRing A]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (x : X) (hx : f.base x = closedPoint A) :
    IsLocalHom ((X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) := by
  rw [const_eq_comp]
  refine ⟨fun a ha => ?_⟩
  rw [RingHom.comp_apply, isUnit_map_iff] at ha
  have h3 : IsUnit (algebraMap A ((Spec.structureSheaf A).presheaf.stalk (f.base x)) a) := ha
  rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (f.base x).asIdeal] at h3
  by_contra hna
  apply h3
  rw [hx]
  exact (IsLocalRing.mem_maximalIdeal a).mpr hna

theorem base_mem_smoothLocus_of_special
    {A₀ A : Type} [CommRing A₀] [CommRing A] [IsLocalRing A₀] [IsLocalRing A]
    (ι : A₀ →+* A) [IsLocalHom ι] (hres : Function.Surjective ((IsLocalRing.residue A).comp ι))
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [LocallyOfFinitePresentation toBase₀] [Flat toBase₀]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A))
    (iso : X ≅ pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    [LocallyOfFinitePresentation toBase]
    (x : X) (hx : toBase.base x = closedPoint A) (hxs : x ∈ toBase.smoothLocus) :
    (iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x ∈ toBase₀.smoothLocus := by
  classical

  let c : A →+* X.presheaf.stalk x :=
    (X.presheaf.germ ⊤ x trivial).hom.comp (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
  let c₀ : A₀ →+* X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) :=
    (X₀.presheaf.germ ⊤ ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) trivial).hom.comp
      (toBase₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom)
  letI algS : Algebra A (X.presheaf.stalk x) := c.toAlgebra
  letI algO : Algebra A₀ (X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)) := c₀.toAlgebra

  have hsq : (iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))) ≫ toBase₀ = toBase ≫ Spec.map (CommRingCat.ofHom ι) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hiso]
  have hx₀ : toBase₀.base ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) = closedPoint A₀ := by
    have : toBase₀.base ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) = (Spec.map (CommRingCat.ofHom ι)).base (toBase.base x) := by
      show ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))) ≫ toBase₀).base x = _
      rw [hsq]; rfl
    rw [this, hx]
    exact IsLocalRing.comap_closedPoint ι

  haveI hFS : Algebra.FormallySmooth A (X.presheaf.stalk x) :=
    (AlgebraicGeometry.mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk toBase x
      (RingEquiv.refl _) (fun r => rfl)).mp hxs

  obtain ⟨hcompat, ⟨e', he'⟩, -, -⟩ :=
    AlgebraicGeometry.exists_ringEquiv_stalk_quotient_map_maximalIdeal_of_iso_pullback_of_residue_surjective
      ι hres X₀ toBase₀ X toBase iso hiso x hx

  have h3 : Algebra.FormallySmooth (A ⧸ maximalIdeal A)
      (X.presheaf.stalk x ⧸ (maximalIdeal A).map (algebraMap A (X.presheaf.stalk x))) :=
    Algebra.FormallySmooth.of_equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (X.presheaf.stalk x) (maximalIdeal A)).symm

  have hle : maximalIdeal A₀ ≤ (maximalIdeal A).comap ι := fun a ha =>
    (IsLocalRing.mem_maximalIdeal _).mpr (fun hu => (IsLocalRing.mem_maximalIdeal _).mp ha ((isUnit_map_iff ι a).mp hu))
  have hge : (maximalIdeal A).comap ι ≤ maximalIdeal A₀ := fun a ha =>
    (IsLocalRing.mem_maximalIdeal _).mpr (fun hu => (IsLocalRing.mem_maximalIdeal _).mp ha (hu.map ι))
  let rq : A₀ ⧸ maximalIdeal A₀ →+* A ⧸ maximalIdeal A := Ideal.quotientMap (maximalIdeal A) ι hle
  have hrq : Function.Bijective rq := by
    refine ⟨Ideal.quotientMap_injective' hge, fun y => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a₀, ha₀⟩ := hres (Ideal.Quotient.mk (maximalIdeal A) a)
    exact ⟨Ideal.Quotient.mk _ a₀, by rw [Ideal.quotientMap_mk]; exact ha₀⟩
  let r : (A₀ ⧸ maximalIdeal A₀) ≃+* (A ⧸ maximalIdeal A) := RingEquiv.ofBijective rq hrq

  have h5 : Algebra.FormallySmooth (A₀ ⧸ maximalIdeal A₀)
      (X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) ⧸ (maximalIdeal A₀).map (algebraMap A₀ (X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)))) := by
    haveI := h3
    refine formallySmooth_transport
      (B₀ := X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) ⧸ (maximalIdeal A₀).map (algebraMap A₀ (X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x))))
      (B := X.presheaf.stalk x ⧸ (maximalIdeal A).map (algebraMap A (X.presheaf.stalk x))) r e' (fun ab => ?_)
    obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective ab
    have e1 : e' (algebraMap (A₀ ⧸ maximalIdeal A₀)
        (X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) ⧸ (maximalIdeal A₀).map (algebraMap A₀ (X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x))))
        (Ideal.Quotient.mk (maximalIdeal A₀) a₀)) =
        Ideal.Quotient.mk _ (((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap x).hom (c₀ a₀)) := by
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient]; exact he' _
    have e2 : ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap x).hom (c₀ a₀) = c (ι a₀) := hcompat a₀
    rw [e1, e2]
    change _ = algebraMap _ _ (rq (Ideal.Quotient.mk _ a₀))
    rw [Ideal.quotientMap_mk, Ideal.Quotient.algebraMap_quotient_map_quotient]
    rfl

  have h6 : Algebra.FormallySmooth (A₀ ⧸ maximalIdeal A₀)
      ((A₀ ⧸ maximalIdeal A₀) ⊗[A₀] X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)) := by
    haveI := h5
    exact Algebra.FormallySmooth.of_equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)) (maximalIdeal A₀))
  haveI hfib : Algebra.FormallySmooth (ResidueField A₀) (ResidueField A₀ ⊗[A₀] X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)) := h6

  have hc₀eq := const_eq_comp A₀ X₀ toBase₀ ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)
  haveI : Module.Flat A₀ (X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)) := by
    have hflat : c₀.Flat := by
      show ((X₀.presheaf.germ ⊤ ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) trivial).hom.comp
        (toBase₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom)).Flat
      rw [hc₀eq]
      refine RingHom.Flat.comp ?_ (Flat.stalkMap toBase₀ ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x))
      change (algebraMap A₀ ((Spec.structureSheaf A₀).presheaf.stalk (toBase₀.base ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)))).Flat
      rw [RingHom.flat_algebraMap_iff]
      exact IsLocalization.flat _ (toBase₀.base ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)).asIdeal.primeCompl
    exact hflat
  haveI : IsLocalHom (algebraMap A₀ (X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x))) :=
    isLocalHom_const A₀ X₀ toBase₀ ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) hx₀

  let U : X₀.Opens := (X₀.affineCover.f (X₀.affineCover.idx ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X₀.affineCover.f _)
  have hxU : (iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x ∈ U := X₀.affineCover.covers ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)
  have hUle : U ≤ toBase₀ ⁻¹ᵁ ⊤ := by simp
  let φP : A₀ →+* Γ(X₀, U) :=
    (toBase₀.appLE ⊤ U hUle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom
  letI algP : Algebra A₀ Γ(X₀, U) := φP.toAlgebra
  letI algPO : Algebra Γ(X₀, U) (X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)) :=
    TopCat.Presheaf.algebra_section_stalk X₀.presheaf ⟨(iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x, hxU⟩
  haveI : IsScalarTower A₀ Γ(X₀, U) (X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    show c₀ = (X₀.presheaf.germ U ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) hxU).hom.comp φP
    have key : toBase₀.appLE ⊤ U hUle ≫ X₀.presheaf.germ U ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) hxU =
        toBase₀.appTop ≫ X₀.presheaf.germ ⊤ ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) trivial := by
      rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
      rfl
    ext a
    have h := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)) key
    simp only [CommRingCat.comp_apply] at h
    exact h.symm
  haveI : Algebra.FinitePresentation A₀ Γ(X₀, U) := by
    have h := Scheme.Hom.finitePresentation_appLE toBase₀ (isAffineOpen_top _) hU hUle
    have h' : φP.FinitePresentation := by
      show (((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv ≫ toBase₀.appLE ⊤ U hUle).hom).FinitePresentation
      exact (RingHom.finitePresentation_respectsIso.cancel_left_isIso
        (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv (toBase₀.appLE ⊤ U hUle)).mpr h
    exact h'
  haveI hloc := hU.isLocalization_stalk ⟨(iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x, hxU⟩

  have h8 : Algebra.FormallySmooth A₀ (X₀.presheaf.stalk ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)) :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
      (P := Γ(X₀, U)) (hU.primeIdealOf ⟨(iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x, hxU⟩).asIdeal.primeCompl
  exact (AlgebraicGeometry.mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk toBase₀ ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x)
    (RingEquiv.refl _) (fun r => rfl)).mpr h8

end BCSmoothAux

namespace BCSmoothAux

theorem mem_smoothLocus_of_base_mem
    {A₀ A : Type} [CommRing A₀] [CommRing A] (ι : A₀ →+* A)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [LocallyOfFinitePresentation toBase₀]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A))
    (iso : X ≅ pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    [LocallyOfFinitePresentation toBase] (x : X)
    (hx : (iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x ∈ toBase₀.smoothLocus) :
    x ∈ toBase.smoothLocus := by
  set pr := iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι)) with hpr
  set V₀ : X₀.Opens := toBase₀.smoothLocus with hV₀

  haveI hsm : Smooth (V₀.ι ≫ toBase₀) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Opens.ι_preimage_self V₀

  have hsq : IsPullback pr toBase toBase₀ (Spec.map (CommRingCat.ofHom ι)) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ iso rfl hiso
    change (iso.hom ≫ pullback.fst _ _) ≫ toBase₀ = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hiso]
  have hsqV : IsPullback (pr ∣_ V₀) ((pr ⁻¹ᵁ V₀).ι ≫ toBase) (V₀.ι ≫ toBase₀) (Spec.map (CommRingCat.ofHom ι)) :=
    (isPullback_morphismRestrict pr V₀).paste_vert hsq
  haveI : Smooth ((pr ⁻¹ᵁ V₀).ι ≫ toBase) :=
    MorphismProperty.of_isPullback (P := @Smooth) hsqV hsm

  have htop : ((pr ⁻¹ᵁ V₀).ι ≫ toBase).smoothLocus = ⊤ := Scheme.Hom.smoothLocus_eq_top _
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at htop
  have hx' : (⟨x, hx⟩ : ↥(pr ⁻¹ᵁ V₀)) ∈ (pr ⁻¹ᵁ V₀).ι ⁻¹ᵁ toBase.smoothLocus := by
    rw [htop]; trivial
  exact hx'

theorem base_mem_smoothLocus_of_generic
    {A₀ A : Type} [CommRing A₀] [CommRing A] (ι : A₀ →+* A) (hι : Function.Injective ι)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [LocallyOfFinitePresentation toBase₀]
    (hgen₀ : ∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A))
    (iso : X ≅ pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    (x : X) (hx : (toBase.base x).asIdeal = ⊥) :
    (iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x ∈ toBase₀.smoothLocus := by
  apply hgen₀
  have hsq : (iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))) ≫ toBase₀ =
      toBase ≫ Spec.map (CommRingCat.ofHom ι) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hiso]
  have : toBase₀.base ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x) =
      (Spec.map (CommRingCat.ofHom ι)).base (toBase.base x) := by
    show ((iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))) ≫ toBase₀).base x = _
    rw [hsq]; rfl
  rw [this]
  show Ideal.comap ι (toBase.base x).asIdeal = ⊥
  rw [hx, Ideal.comap_bot_of_injective ι hι]

theorem eq_maximalIdeal_of_ne_bot {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (P : Ideal ↥A) [P.IsPrime] (hP : P ≠ ⊥) : P = maximalIdeal ↥A := by
  refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
  intro a ha
  obtain ⟨b, hbP, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  obtain ⟨n, c, hc⟩ := hrk a b ha hb0
  have : a ^ n ∈ P := by rw [hc]; exact Ideal.mul_mem_right _ _ hbP
  exact Ideal.IsPrime.mem_of_pow_mem ‹_› n this

end BCSmoothAux

open AlgebraicCurve in
theorem solution
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))

    (hO : Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))

    (hgen₀ : ∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus)

    (hsm₀ : ∀ η₀ : X₀, toBase₀.base η₀ = closedPoint A₀ → (∃ y : X₀, η₀ ⤳ y ∧ y ≠ η₀) → η₀ ∈ toBase₀.smoothLocus)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    [hlfp : LocallyOfFinitePresentation toBase] :
    let pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))
    ∀ x : X, x ∈ toBase.smoothLocus ↔ pr.base x ∈ toBase₀.smoothLocus := by
  intro pr x
  constructor
  · intro hxs
    rcases Classical.em ((toBase.base x).asIdeal = ⊥) with hgen | hne
    · exact BCSmoothAux.base_mem_smoothLocus_of_generic ι hι X₀ toBase₀ hgen₀ X toBase iso hiso x hgen
    · have hxcl : toBase.base x = closedPoint ↥A :=
        PrimeSpectrum.ext (BCSmoothAux.eq_maximalIdeal_of_ne_bot A hrk _ hne)
      exact BCSmoothAux.base_mem_smoothLocus_of_special ι hres X₀ toBase₀ X toBase iso hiso x hxcl hxs
  · intro h
    exact BCSmoothAux.mem_smoothLocus_of_base_mem ι X₀ toBase₀ X toBase iso hiso x h

end S_AlgebraicGeometry_mem_smoothLocus_iff_base_mem_smoothLocus_of_iso_pullback_of_isDiscreteValuationRing
end P2MW
export P2MW.S_AlgebraicGeometry_mem_smoothLocus_iff_base_mem_smoothLocus_of_iso_pullback_of_isDiscreteValuationRing (solution)
