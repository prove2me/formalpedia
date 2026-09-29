-- Prove2me | solution 1 for AlgebraicGeometry.stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f5e23c93-278b-5823-a7c2-3defa3903327

import Mathlib
import Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped TensorProduct

namespace StalkPkg

noncomputable abbrev cW (W : Type u) [CommRing W] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of W)) (x : ↥X) :
    W →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)

theorem cW_apply (W : Type u) [CommRing W] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of W)) (x : ↥X) (a : W) :
    cW W f x a = (f.stalkMap x).hom ((StructureSheaf.toStalk W (f.base x)).hom a) := by
  simp only [RingHom.coe_comp, Function.comp_apply, StructureSheaf.toStalk, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rfl

theorem cW_eq (W : Type u) [CommRing W] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of W)) (x : ↥X) :
    cW W f x = (f.stalkMap x).hom.comp (StructureSheaf.toStalk W (f.base x)).hom :=
  RingHom.ext fun a => cW_apply W f x a

theorem isLocalHom_toStalk_of_eq_closedPoint (W : Type u) [CommRing W] [IsLocalRing W]
    (y : PrimeSpectrum W) (hy : y = closedPoint W) :
    IsLocalHom (StructureSheaf.toStalk W y).hom := by
  subst hy
  constructor
  intro a ha
  have h := (IsLocalization.AtPrime.isUnit_to_map_iff
    ((Spec.structureSheaf W).presheaf.stalk (closedPoint W)) (closedPoint W).asIdeal a).mp ha
  by_contra hna
  exact h ((IsLocalRing.mem_maximalIdeal a).mpr hna)

theorem flat_toStalk (W : Type u) [CommRing W] (y : PrimeSpectrum W) :
    (StructureSheaf.toStalk W y).hom.Flat :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat ((Spec.structureSheaf W).presheaf.stalk y) y.asIdeal.primeCompl)

theorem main (W : Type u) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
    [IsAlgClosed (ResidueField W)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of W)) [SmoothOfRelativeDimension 1 f]
    (x : ↥X) (hx : f.base x = closedPoint W) (hxc : IsClosed ({x} : Set ↥X)) :
    letI : Algebra W (X.presheaf.stalk x) := (cW W f x).toAlgebra
    IsNoetherianRing (X.presheaf.stalk x) ∧ IsLocalHom (algebraMap W (X.presheaf.stalk x)) ∧
      Module.Flat W (X.presheaf.stalk x) ∧
      Function.Surjective ((IsLocalRing.residue (X.presheaf.stalk x)).comp (algebraMap W (X.presheaf.stalk x))) ∧
      ∃ t : X.presheaf.stalk x,
        maximalIdeal (X.presheaf.stalk x) = (maximalIdeal W).map (algebraMap W (X.presheaf.stalk x)) ⊔ Ideal.span {t} ∧
        ringKrullDim (X.presheaf.stalk x ⧸ (maximalIdeal W).map (algebraMap W (X.presheaf.stalk x))) = 1 := by
  letI inst : Algebra W (X.presheaf.stalk x) := (cW W f x).toAlgebra
  have halg : algebraMap W (X.presheaf.stalk x) = cW W f x := rfl
  haveI : Smooth f := SmoothOfRelativeDimension.smooth (n := 1) (f := f)

  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have h1 : IsNoetherianRing (X.presheaf.stalk x) := inferInstance

  have hc := cW_eq W f x
  have h2 : IsLocalHom (algebraMap W (X.presheaf.stalk x)) := by
    rw [halg, hc]
    haveI : IsLocalHom (f.stalkMap x).hom := inferInstance
    haveI h' : IsLocalHom (StructureSheaf.toStalk (↑(CommRingCat.of W)) (f.base x)).hom :=
      isLocalHom_toStalk_of_eq_closedPoint W (f.base x) hx
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ inferInstance h'

  have h3 : Module.Flat W (X.presheaf.stalk x) := by
    have : (cW W f x).Flat := by
      rw [hc]
      exact RingHom.Flat.comp (flat_toStalk W (f.base x)) (Flat.stalkMap f x)
    exact this

  classical
  obtain ⟨U, hU, V, hV, hxV, hle, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp (hx ▸ hle hxV)

  let eΓ : W ≃+* Γ(Spec (CommRingCat.of W), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv
  let ψ : W →+* Γ(X, V) := (f.appLE ⊤ V hle).hom.comp eΓ.toRingHom
  have hψstd : ψ.IsStandardSmoothOfRelativeDimension 1 :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ eΓ hstd
  letI algWA : Algebra W Γ(X, V) := ψ.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 W Γ(X, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hψstd
  haveI : Algebra.IsStandardSmooth W Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI : Algebra.FiniteType W Γ(X, V) := inferInstance

  let p : Ideal Γ(X, V) := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  haveI hpmax : p.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hxc
  letI algAO : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hxV).hom.toAlgebra
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x) p := hV.isLocalization_stalk ⟨x, hxV⟩

  have hcomp : cW W f x = (algebraMap Γ(X, V) (X.presheaf.stalk x)).comp ψ := by
    apply RingHom.ext
    intro a
    show (X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a)) =
      (X.presheaf.germ V x hxV).hom ((f.appLE ⊤ V hle).hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a))
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply (f.appLE ⊤ V hle), Scheme.Hom.appLE,
      Category.assoc, X.presheaf.germ_res]
    rfl
  haveI : IsScalarTower W Γ(X, V) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq (fun a => by
    show cW W f x a = algebraMap Γ(X, V) (X.presheaf.stalk x) (ψ a)
    rw [hcomp]; rfl)

  have hmp : (maximalIdeal W).map ψ ≤ p := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hna : ¬ IsUnit (cW W f x a) := fun hu => ((IsLocalRing.mem_maximalIdeal a).mp ha) (h2.map_nonunit a hu)
    have hmem : cW W f x a ∈ maximalIdeal (X.presheaf.stalk x) := (IsLocalRing.mem_maximalIdeal _).mpr hna
    rw [hcomp] at hmem
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x) p (ψ a)).mp hmem
  refine ⟨h1, h2, h3, ?_, ?_⟩
  ·
    let k := ResidueField W
    let φ : k →+* Γ(X, V) ⧸ p := Ideal.quotientMap p ψ (Ideal.map_le_iff_le_comap.mp hmp)
    letI algk : Algebra k (Γ(X, V) ⧸ p) := φ.toAlgebra
    haveI : IsScalarTower W k (Γ(X, V) ⧸ p) := IsScalarTower.of_algebraMap_eq (fun a => rfl)
    haveI : Algebra.FiniteType W (Γ(X, V) ⧸ p) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ W p) (Ideal.Quotient.mkₐ_surjective W p)
    haveI : Algebra.FiniteType k (Γ(X, V) ⧸ p) := Algebra.FiniteType.of_restrictScalars_finiteType W k _
    have hφ : Function.Surjective φ := by
      letI : Field (Γ(X, V) ⧸ p) := Ideal.Quotient.field p
      have hfin := finite_of_finite_type_of_isJacobsonRing k (Γ(X, V) ⧸ p)
      have hint := @Algebra.IsIntegral.of_finite k (Γ(X, V) ⧸ p) _ _ _ hfin
      exact (@IsAlgClosed.algebraMap_bijective_of_isIntegral k (Γ(X, V) ⧸ p) _ _ _ _ _ hint).2
    let e := IsLocalization.AtPrime.equivQuotMaximalIdeal p (X.presheaf.stalk x)
    intro z
    obtain ⟨y, rfl⟩ := e.surjective z
    obtain ⟨c, rfl⟩ := hφ y
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨w, ?_⟩
    show Ideal.Quotient.mk _ (cW W f x w) = e (φ (Ideal.Quotient.mk _ w))
    rw [hcomp]
    exact (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk p (X.presheaf.stalk x) (ψ w)).symm
  ·
    let k := ResidueField W
    let A := Γ(X, V)
    let O := X.presheaf.stalk x
    let I : Ideal A := (maximalIdeal W).map (algebraMap W A)
    let J : Ideal O := (maximalIdeal W).map (algebraMap W O)
    have hIJ : I.map (algebraMap A O) = J := by
      show ((maximalIdeal W).map (algebraMap W A)).map (algebraMap A O) = (maximalIdeal W).map (algebraMap W O)
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    have hIp : I ≤ p := hmp

    let e : (A ⧸ I) ≃+* k ⊗[W] A :=
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (maximalIdeal W)).toRingEquiv.trans
        (Algebra.TensorProduct.comm W A k).toRingEquiv
    let π : A →+* k ⊗[W] A := e.toRingHom.comp (Ideal.Quotient.mk I)
    have hπsurj : Function.Surjective π := e.surjective.comp Ideal.Quotient.mk_surjective
    have hπker : ∀ a : A, π a = 0 ↔ a ∈ I := fun a => by
      show e (Ideal.Quotient.mk I a) = 0 ↔ a ∈ I
      rw [e.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    have hπp : ∀ a : A, π a ∈ p.map π ↔ a ∈ p := fun a => by
      constructor
      · intro h
        obtain ⟨y, hy, hya⟩ := (Ideal.mem_map_iff_of_surjective π hπsurj).mp h
        have : a - y ∈ I := (hπker _).mp (by rw [map_sub, hya, sub_self])
        simpa using p.add_mem (hIp this) hy
      · exact fun h => Ideal.mem_map_of_mem π h
    let P' : Ideal (k ⊗[W] A) := p.map π
    have hP'ne : P' ≠ ⊤ := by
      intro htop
      have h1 : π 1 ∈ P' := htop ▸ Submodule.mem_top
      exact hpmax.ne_top ((Ideal.eq_top_iff_one p).mpr ((hπp 1).mp h1))
    haveI hP'max : P'.IsMaximal := (Ideal.map_eq_top_or_isMaximal_of_surjective π hπsurj hpmax).resolve_left hP'ne

    let Q := O ⧸ I.map (algebraMap A O)
    haveI hQ : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) p.primeCompl) Q := inferInstance
    letI algQ : Algebra (k ⊗[W] A) Q := ((algebraMap (A ⧸ I) Q).comp e.symm.toRingHom).toAlgebra
    have hM : Submonoid.map e (Algebra.algebraMapSubmonoid (A ⧸ I) p.primeCompl) = P'.primeCompl := by
      ext z
      simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, Ideal.mem_primeCompl_iff]
      constructor
      · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
        show π a ∉ P'
        exact fun h => ha ((hπp a).mp h)
      · intro hz
        obtain ⟨a, rfl⟩ := hπsurj z
        exact ⟨Ideal.Quotient.mk I a, ⟨a, fun h => hz ((hπp a).mpr h), rfl⟩, rfl⟩
    haveI hlocQ : IsLocalization.AtPrime Q P' := by
      have := IsLocalization.isLocalization_of_base_ringEquiv (Algebra.algebraMapSubmonoid (A ⧸ I) p.primeCompl) Q e
      rwa [hM] at this
    obtain ⟨hdomL, hdvrL⟩ :=
      Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime (k := k) P'
    let eQ : Localization.AtPrime P' ≃+* Q :=
      (IsLocalization.algEquiv P'.primeCompl (Localization.AtPrime P') Q).toRingEquiv
    haveI : IsDomain Q := MulEquiv.isDomain (Localization.AtPrime P') eQ.symm.toMulEquiv
    haveI : IsDiscreteValuationRing Q := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eQ

    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Q
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective ϖ
    refine ⟨t, ?_, ?_⟩
    · have hmax : Ideal.comap (Ideal.Quotient.mk (I.map (algebraMap A O))) (maximalIdeal Q) = maximalIdeal O :=
        IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
      rw [← hmax, hϖ.maximalIdeal_eq, ← ht, ← Set.image_singleton, ← Ideal.map_span,
        Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, hIJ,
        sup_comm]
    · have hdim : ringKrullDim Q = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one Q
      exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hIJ)).symm.trans hdim

end StalkPkg

theorem solution
    (W : Type u) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAdicComplete (maximalIdeal W) W]
    [IsAlgClosed (ResidueField W)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of W)) [SmoothOfRelativeDimension 1 f]
    (x : ↥X) (hx : f.base x = closedPoint W) (hxc : IsClosed ({x} : Set ↥X)) :
    letI : Algebra W (X.presheaf.stalk x) :=
      ((X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)).toAlgebra
    IsNoetherianRing (X.presheaf.stalk x) ∧ IsLocalHom (algebraMap W (X.presheaf.stalk x)) ∧
      Module.Flat W (X.presheaf.stalk x) ∧
      Function.Surjective ((IsLocalRing.residue (X.presheaf.stalk x)).comp (algebraMap W (X.presheaf.stalk x))) ∧
      ∃ t : X.presheaf.stalk x,
        maximalIdeal (X.presheaf.stalk x) = (maximalIdeal W).map (algebraMap W (X.presheaf.stalk x)) ⊔ Ideal.span {t} ∧
        ringKrullDim (X.presheaf.stalk x ⧸ (maximalIdeal W).map (algebraMap W (X.presheaf.stalk x))) = 1 :=
  StalkPkg.main W f x hx hxc

end S_AlgebraicGeometry_stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_stalk_flat_and_maximalIdeal_eq_sup_span_of_smoothOfRelativeDimension_one (solution)
