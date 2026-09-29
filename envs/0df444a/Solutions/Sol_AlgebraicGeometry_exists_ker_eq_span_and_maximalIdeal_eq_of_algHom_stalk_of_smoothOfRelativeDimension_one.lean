-- Prove2me | solution 1 for AlgebraicGeometry.exists_ker_eq_span_and_maximalIdeal_eq_of_algHom_stalk_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3e3e5a5d-fe64-5a33-b54e-db4da1b8de79

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ker_eq_span_and_maximalIdeal_eq_of_algHom_stalk_of_smoothOfRelativeDimension_one

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace P2Body
namespace CotSec

open TensorProduct

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

theorem kerCotangentToTensor_bijective [Algebra.FormallySmooth R A] (e : A →ₐ[R] R) :
    letI : Algebra A R := e.toRingHom.toAlgebra
    Function.Bijective (KaehlerDifferential.kerCotangentToTensor R A R) := by
  letI : Algebra A R := e.toRingHom.toAlgebra
  haveI : IsScalarTower R A R := IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  have hsurj : Function.Surjective (algebraMap A R) := fun r => ⟨algebraMap R A r, e.commutes r⟩
  haveI : Subsingleton Ω[R⁄R] :=
    KaehlerDifferential.subsingleton_of_surjective (R := R) (S := R) Function.surjective_id
  constructor
  · obtain ⟨l, hl⟩ :=
      (Algebra.FormallySmooth.iff_split_injection (R := R) (P := A) (A := R) hsurj).mp inferInstance
    exact Function.LeftInverse.injective (g := l) fun x => LinearMap.congr_fun hl x
  · intro y
    exact (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A R hsurj y).mp
      (Subsingleton.elim _ _)

theorem free_tensor_kaehlerDifferential [IsLocalRing R] (e : A →ₐ[R] R)
    (hloc : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f) (algebraMap R A)) :
    letI : Algebra A R := e.toRingHom.toAlgebra
    Module.Free R (R ⊗[A] Ω[A⁄R]) ∧ Module.finrank R (R ⊗[A] Ω[A⁄R]) = 1 := by
  letI : Algebra A R := e.toRingHom.toAlgebra
  haveI : IsScalarTower R A R := IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  obtain ⟨s, hs, hP⟩ := hloc
  have hex : ∃ t ∈ s, IsUnit (e t) := by
    by_contra hcon
    push Not at hcon
    have hle : Ideal.map e.toRingHom (Ideal.span s) ≤ IsLocalRing.maximalIdeal R := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨t, ht, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).mpr (hcon t ht)
    rw [hs, Ideal.map_top, top_le_iff] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle
  obtain ⟨t, ht, hunit⟩ := hex
  have hstd := hP t ht
  set At := Localization.Away t with hAt
  rw [← IsScalarTower.algebraMap_eq R A At] at hstd
  haveI hstd' : Algebra.IsStandardSmoothOfRelativeDimension 1 R At :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hstd
  haveI : Algebra.IsStandardSmooth R At :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let e' : At →+* R := IsLocalization.Away.lift t (g := e.toRingHom) hunit
  haveI : Nontrivial At := e'.domain_nontrivial
  have hrank : Module.rank At Ω[At⁄R] = 1 := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := At) 1
  have hfin : Module.finrank At Ω[At⁄R] = 1 := Module.finrank_eq_of_rank_eq (by simpa using hrank)
  letI : Algebra At R := e'.toAlgebra
  haveI : IsScalarTower A At R :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp t hunit).symm
  haveI : IsScalarTower R At R := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [IsScalarTower.algebraMap_eq R A At, ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A At R,
      ← IsScalarTower.algebraMap_eq R A R]
  haveI : Algebra.FormallyEtale A At := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  let i1 : R ⊗[At] (At ⊗[A] Ω[A⁄R]) ≃ₗ[R] R ⊗[A] Ω[A⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A At R R Ω[A⁄R]
  let i2 : R ⊗[At] (At ⊗[A] Ω[A⁄R]) ≃ₗ[R] R ⊗[At] Ω[At⁄R] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R)
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A At)
  let i : R ⊗[A] Ω[A⁄R] ≃ₗ[R] R ⊗[At] Ω[At⁄R] := i1.symm ≪≫ₗ i2
  refine ⟨Module.Free.of_equiv i.symm, ?_⟩
  rw [i.finrank_eq, Module.finrank_baseChange, hfin]

theorem free_cotangent_ker [IsLocalRing R] [Algebra.FormallySmooth R A] (e : A →ₐ[R] R)
    (hloc : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f) (algebraMap R A)) :
    Module.Free R (RingHom.ker e.toRingHom).Cotangent ∧
      Module.finrank R (RingHom.ker e.toRingHom).Cotangent = 1 := by
  letI : Algebra A R := e.toRingHom.toAlgebra
  haveI : IsScalarTower R A R := IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  obtain ⟨hfree, hrank⟩ := free_tensor_kaehlerDifferential e hloc
  let f : (RingHom.ker e.toRingHom).Cotangent ≃ₗ[R] R ⊗[A] Ω[A⁄R] :=
    (LinearEquiv.ofBijective (KaehlerDifferential.kerCotangentToTensor R A R)
      (kerCotangentToTensor_bijective e)).restrictScalars R
  exact ⟨Module.Free.of_equiv f.symm, f.finrank_eq.trans hrank⟩

end P2Body.CotSec

namespace P2Body
namespace GenKerAux

theorem exists_generator {R A : Type*} [CommRing R] [Nontrivial R] [CommRing A] [Algebra R A] (e : A →ₐ[R] R)
    [Module.Free R (RingHom.ker e.toRingHom).Cotangent]
    (he : Module.finrank R (RingHom.ker e.toRingHom).Cotangent = 1) :
    ∃ t₀ : A, e t₀ = 0 ∧ RingHom.ker e.toRingHom ≤ Ideal.span {t₀} ⊔ RingHom.ker e.toRingHom ^ 2 := by
  set I : Ideal A := RingHom.ker e.toRingHom with hI
  let b := Module.basisUnique Unit he
  obtain ⟨t, ht⟩ := I.toCotangent_surjective (b default)
  refine ⟨t, t.2, fun x hx => ?_⟩

  set r : R := b.repr (I.toCotangent ⟨x, hx⟩) default with hr
  have h1 : I.toCotangent ⟨x, hx⟩ = r • I.toCotangent t := by
    rw [ht]
    simpa using (b.sum_repr (I.toCotangent ⟨x, hx⟩)).symm
  rw [← LinearMap.map_smul_of_tower] at h1
  have h2 := (I.toCotangent_eq).mp h1

  have hx' : x = ((r • t : I) : A) + (x - ((r • t : I) : A)) := by abel
  rw [hx']
  refine Submodule.add_mem_sup ?_ h2
  rw [Submodule.coe_smul_of_tower, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end P2Body.GenKerAux

namespace P2Body

open TensorProduct

@[reducible] private noncomputable def _root_.P2Body.stalkAlgebra {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
    (x : X) : Algebra R (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra

p2m_export "P2Body" "stalkAlgebra"

theorem Lpi {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
    (σ : Spec (CommRingCat.of R) ⟶ X) (hσ : σ ≫ c = 𝟙 _)
    (s : Spec (CommRingCat.of R)) (hs : IsClosed ({s} : Set (Spec (CommRingCat.of R)))) :
    letI := stalkAlgebra c (σ.base s)
    ∃ π : X.presheaf.stalk (σ.base s) →ₐ[R] R, RingHom.ker (Scheme.Hom.stalkMap σ s).hom ≤ RingHom.ker π := by

  have hs' : s = IsLocalRing.closedPoint R :=
    PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal s).mp hs))
  subst hs'
  letI := stalkAlgebra c (σ.base (IsLocalRing.closedPoint R))

  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appTop ≫
      X.presheaf.germ ⊤ (σ.base (IsLocalRing.closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo σ = 𝟙 _ := by
    rw [Scheme.germ_stalkClosedPointTo σ ⊤ trivial]
    have h1 : c.appTop ≫ σ.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, hσ, Scheme.Hom.id_appTop]
    erw [reassoc_of% h1]
    simp
  refine ⟨{ (Scheme.stalkClosedPointTo σ).hom with
      commutes' := fun r => ?_ }, ?_⟩
  ·
    show (Scheme.stalkClosedPointTo σ).hom
        ((X.presheaf.germ ⊤ (σ.base (IsLocalRing.closedPoint R)) trivial).hom
          (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = r
    have := congrArg (fun φ => φ.hom r) key
    simpa using this
  ·
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    show (Scheme.stalkClosedPointTo σ).hom x = 0
    rw [Scheme.stalkClosedPointTo, CommRingCat.comp_apply]
    erw [hx]
    exact map_zero _

theorem LS' {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 c] (V : X.Opens) (hV : IsAffineOpen V) (y : V) :
    letI := stalkAlgebra c (y : X)
    Algebra.FormallySmooth R (X.presheaf.stalk (y : X)) ∧
    Module.Finite (X.presheaf.stalk (y : X)) Ω[(X.presheaf.stalk (y : X))⁄R] ∧
    ∀ π : X.presheaf.stalk (y : X) →ₐ[R] R,
      Module.Free R (RingHom.ker π.toRingHom).Cotangent ∧ Module.finrank R (RingHom.ker π.toRingHom).Cotangent = 1 := by
  letI instRS := stalkAlgebra c (y : X)
  have hxV : (y : X) ∈ V := y.2

  letI algA : Algebra R Γ(X, V) := ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom.toAlgebra
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have hsm : (c.appLE ⊤ V le_top).hom.Smooth :=
    Smooth.smooth_appLE (f := c) (isAffineOpen_top (Spec (.of R))) hV le_top
  haveI fsA : Algebra.FormallySmooth R Γ(X, V) := by
    have h2 : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom.FormallySmooth := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr hsm.formallySmooth
    exact h2.toAlgebra
  haveI ftA : Algebra.FiniteType R Γ(X, V) := by
    have h2 : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom.FiniteType := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.finiteType_respectsIso.cancel_left_isIso _ _).mpr
        (RingHom.FiniteType.of_finitePresentation hsm.finitePresentation)
    exact h2
  have hloc : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f)
      (algebraMap R Γ(X, V)) := by
    have h1 : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f)
        (c.appLE ⊤ V le_top).hom :=
      HasRingHomProperty.appLE (@SmoothOfRelativeDimension 1) c inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    have h2 : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f)
        ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom := by
      rw [CommRingCat.hom_comp]
      exact ((RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso).cancel_left_isIso
        _ _).mpr h1
    exact h2

  haveI hIL : IsLocalization.AtPrime (X.presheaf.stalk (y : X)) (hV.primeIdealOf y).asIdeal := hV.isLocalization_stalk y
  haveI hST : IsScalarTower R Γ(X, V) (X.presheaf.stalk (y : X)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have key : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appTop) ≫ X.presheaf.germ ⊤ (y : X) trivial =
        ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top) ≫ X.presheaf.germ V (y : X) hxV := by
      simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
      rfl
    show (X.presheaf.germ ⊤ (y : X) trivial).hom.comp (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) =
      (X.presheaf.germ V (y : X) hxV).hom.comp (((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom)
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, key]

  haveI fsAS : Algebra.FormallySmooth Γ(X, V) (X.presheaf.stalk (y : X)) :=
    Algebra.FormallySmooth.of_isLocalization (hV.primeIdealOf y).asIdeal.primeCompl
  haveI fsS : Algebra.FormallySmooth R (X.presheaf.stalk (y : X)) :=
    Algebra.FormallySmooth.comp R Γ(X, V) (X.presheaf.stalk (y : X))

  haveI : Algebra.EssFiniteType Γ(X, V) (X.presheaf.stalk (y : X)) :=
    Algebra.EssFiniteType.of_isLocalization _ (hV.primeIdealOf y).asIdeal.primeCompl
  haveI : Algebra.EssFiniteType R (X.presheaf.stalk (y : X)) :=
    Algebra.EssFiniteType.comp R Γ(X, V) (X.presheaf.stalk (y : X))
  refine ⟨fsS, inferInstance, fun π => ?_⟩

  let eA : Γ(X, V) →ₐ[R] R := π.comp (IsScalarTower.toAlgHom R Γ(X, V) (X.presheaf.stalk (y : X)))
  obtain ⟨hfreeA, hrankA⟩ := CotSec.free_tensor_kaehlerDifferential eA hloc

  letI : Algebra Γ(X, V) R := eA.toRingHom.toAlgebra
  letI : Algebra (X.presheaf.stalk (y : X)) R := π.toRingHom.toAlgebra
  haveI : IsScalarTower R Γ(X, V) R := IsScalarTower.of_algebraMap_eq' eA.comp_algebraMap.symm
  haveI : IsScalarTower R (X.presheaf.stalk (y : X)) R := IsScalarTower.of_algebraMap_eq' π.comp_algebraMap.symm
  haveI : IsScalarTower Γ(X, V) (X.presheaf.stalk (y : X)) R := IsScalarTower.of_algebraMap_eq' (by rfl)
  haveI : Algebra.FormallyEtale Γ(X, V) (X.presheaf.stalk (y : X)) :=
    Algebra.FormallyEtale.of_isLocalization (hV.primeIdealOf y).asIdeal.primeCompl
  let S := X.presheaf.stalk (y : X)
  let i1 : R ⊗[S] (S ⊗[Γ(X, V)] Ω[Γ(X, V)⁄R]) ≃ₗ[R] R ⊗[Γ(X, V)] Ω[Γ(X, V)⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, V) S R R Ω[Γ(X, V)⁄R]
  let i2 : R ⊗[S] (S ⊗[Γ(X, V)] Ω[Γ(X, V)⁄R]) ≃ₗ[R] R ⊗[S] Ω[S⁄R] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R)
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Γ(X, V) S)
  let i : R ⊗[Γ(X, V)] Ω[Γ(X, V)⁄R] ≃ₗ[R] R ⊗[S] Ω[S⁄R] := i1.symm ≪≫ₗ i2
  haveI hfreeS : Module.Free R (R ⊗[S] Ω[S⁄R]) := Module.Free.of_equiv i
  have hrankS : Module.finrank R (R ⊗[S] Ω[S⁄R]) = 1 := by rw [← i.finrank_eq, hrankA]

  let f : (RingHom.ker π.toRingHom).Cotangent ≃ₗ[R] R ⊗[S] Ω[S⁄R] :=
    (LinearEquiv.ofBijective (KaehlerDifferential.kerCotangentToTensor R S R)
      (CotSec.kerCotangentToTensor_bijective π)).restrictScalars R
  exact ⟨Module.Free.of_equiv f.symm, f.finrank_eq.trans hrankS⟩

theorem LS {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 c] (x : X) :
    letI := stalkAlgebra c x
    Algebra.FormallySmooth R (X.presheaf.stalk x) ∧
    Module.Finite (X.presheaf.stalk x) Ω[(X.presheaf.stalk x)⁄R] ∧
    ∀ π : X.presheaf.stalk x →ₐ[R] R,
      Module.Free R (RingHom.ker π.toRingHom).Cotangent ∧ Module.finrank R (RingHom.ker π.toRingHom).Cotangent = 1 := by
  obtain ⟨V, hVmem, hxV, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (TopologicalSpace.Opens.mem_top x)
  exact LS' c V hVmem ⟨x, hxV⟩

end P2Body

namespace SecParam

theorem eq_of_retraction_of_ker_le {A S : Type*} [CommRing A] [CommRing S] (ι : A →+* S) (π π' : S →+* A)
    (hπ : ∀ a, π (ι a) = a) (hπ' : ∀ a, π' (ι a) = a) (h : RingHom.ker π' ≤ RingHom.ker π) : π = π' := by
  ext z
  have hz : z - ι (π' z) ∈ RingHom.ker π' := by
    rw [RingHom.mem_ker, map_sub, hπ', sub_self]
  have hz' := h hz
  rw [RingHom.mem_ker, map_sub, hπ] at hz'
  exact sub_eq_zero.mp hz'

theorem eq_span_of_le_span_sup_sq {S : Type*} [CommRing S] [IsLocalRing S] {I : Ideal S} (hfg : I.FG)
    (hI : I ≤ maximalIdeal S) {t : S} (ht : t ∈ I) (hle : I ≤ Ideal.span {t} ⊔ I ^ 2) : I = Ideal.span {t} := by
  apply le_antisymm _ ((Ideal.span_singleton_le_iff_mem _).mpr ht)
  have hjac : I ≤ (⊥ : Ideal S).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact hI
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac (by rwa [Ideal.smul_eq_mul, ← pow_two])

theorem maximalIdeal_eq_ker_sup_map {A S : Type*} [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S]
    (ι : A →+* S) (π : S →+* A) (hπ : ∀ a, π (ι a) = a) :
    maximalIdeal S = RingHom.ker π ⊔ (maximalIdeal A).map ι := by
  have hkle : RingHom.ker π ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)
  apply le_antisymm
  · intro z hz
    have hk : z - ι (π z) ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, map_sub, hπ, sub_self]
    by_cases hu : IsUnit (π z)
    · exfalso
      have h1 : ι (π z) ∈ maximalIdeal S := by
        have e : ι (π z) = z - (z - ι (π z)) := by ring
        rw [e]
        exact sub_mem hz (hkle hk)
      exact (IsLocalRing.mem_maximalIdeal _).mp h1 (hu.map ι)
    · have hm : π z ∈ maximalIdeal A := hu
      have e : z = (z - ι (π z)) + ι (π z) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hk) (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hm))
  · refine sup_le hkle ?_
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun h =>
      (IsLocalRing.mem_maximalIdeal _).mp ha (by simpa [hπ] using h.map π)

theorem bijective_toStalk_closedPoint (A : Type u) [CommRing A] [IsLocalRing A] :
    Function.Bijective (StructureSheaf.toStalk A (closedPoint A)).hom := by
  letI : Algebra A ((Spec.structureSheaf A).presheaf.stalk (closedPoint A)) := StructureSheaf.stalkAlgebra A (closedPoint A)
  haveI : IsLocalization.AtPrime ((Spec.structureSheaf A).presheaf.stalk (closedPoint A)) (closedPoint A).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A (closedPoint A)
  have hM : (closedPoint A).asIdeal.primeCompl ≤ nonZeroDivisors A := fun u hu =>
    (show IsUnit u from not_not.mp hu).mem_nonZeroDivisors
  change Function.Bijective (algebraMap A ((Spec.structureSheaf A).presheaf.stalk (closedPoint A)))
  refine ⟨IsLocalization.injective _ hM, fun z => ?_⟩
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (closedPoint A).asIdeal.primeCompl z
  have hu : IsUnit (u : A) := not_not.mp u.2
  refine ⟨a * ↑hu.unit⁻¹, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]

theorem fg_ker_algHom_stalk {A : Type u} [CommRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    [LocallyOfFinitePresentation c] (x : X)
    (π : letI : Algebra A (X.presheaf.stalk x) := ((X.presheaf.germ ⊤ x trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
      X.presheaf.stalk x →ₐ[A] A) :
    letI : Algebra A (X.presheaf.stalk x) := ((X.presheaf.germ ⊤ x trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
    (RingHom.ker π.toRingHom).FG := by
  classical
  let S := X.presheaf.stalk x
  let algA : A →+* S := (X.presheaf.germ ⊤ x trivial).hom.comp (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
  letI : Algebra A S := algA.toAlgebra
  have hret : ∀ a, π (algA a) = a := fun a => π.commutes a
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  have hVle : V ≤ c ⁻¹ᵁ ⊤ := le_top
  have hfp : (c.appLE ⊤ V hVle).hom.FinitePresentation :=
    HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) c inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ hVle
  let algB : A →+* Γ(X, V) := (c.appLE ⊤ V hVle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hfpB : algB.FinitePresentation :=
    hfp.comp (RingHom.FinitePresentation.of_bijective (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.bijective)
  letI : Algebra Γ(X, V) S := (X.presheaf.germ V x hxV).hom.toAlgebra
  haveI : IsLocalization.AtPrime S (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  have hcompat : ∀ a, algebraMap Γ(X, V) S (algB a) = algA a := by
    intro a
    show (X.presheaf.germ V x hxV).hom ((c.appLE ⊤ V hVle).hom _) = (X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom _)
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
    rfl
  letI : Algebra A Γ(X, V) := algB.toAlgebra
  haveI : Algebra.FinitePresentation A Γ(X, V) := hfpB
  let ψ : Γ(X, V) →ₐ[A] A :=
    { π.toRingHom.comp (algebraMap Γ(X, V) S) with
      commutes' := fun a => by
        show π (algebraMap Γ(X, V) S (algB a)) = a
        rw [hcompat]
        exact hret a }
  have hψsurj : Function.Surjective ψ := fun a => ⟨algB a, by
    show π (algebraMap Γ(X, V) S (algB a)) = a
    rw [hcompat]
    exact hret a⟩
  have hJ : (RingHom.ker ψ.toRingHom).FG := Algebra.FinitePresentation.ker_fG_of_surjective ψ hψsurj
  have hmap : RingHom.ker π.toRingHom = (RingHom.ker ψ.toRingHom).map (algebraMap Γ(X, V) S) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨b, u, rfl⟩ := IsLocalization.exists_mk'_eq (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl z
      have hb : b ∈ RingHom.ker ψ.toRingHom := by
        have e := IsLocalization.mk'_spec S b u
        have e' := congrArg π e
        rw [map_mul] at e'
        have hz' : π (IsLocalization.mk' S b u) = 0 := hz
        rw [hz', zero_mul] at e'
        exact e'.symm
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb)
    · rw [Ideal.map_le_iff_le_comap]
      intro b hb
      exact hb
  rw [hmap]
  exact hJ.map _

end SecParam

open P2Body SecParam in

theorem solution
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    [SmoothOfRelativeDimension 1 c] (x : X)
    (π : letI : Algebra A (X.presheaf.stalk x) := ((X.presheaf.germ ⊤ x trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
      X.presheaf.stalk x →ₐ[A] A) :
    letI : Algebra A (X.presheaf.stalk x) := ((X.presheaf.germ ⊤ x trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
    ∃ t : X.presheaf.stalk x,
      RingHom.ker π.toRingHom = Ideal.span {t} ∧
      maximalIdeal (X.presheaf.stalk x) =
        Ideal.span {t} ⊔ (maximalIdeal A).map ((X.presheaf.germ ⊤ x trivial).hom.comp
          (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) := by
  classical
  letI := P2Body.stalkAlgebra c x
  let algA : A →+* X.presheaf.stalk x := (X.presheaf.germ ⊤ x trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
  obtain ⟨-, -, hcot⟩ := P2Body.LS c x
  obtain ⟨hfree, hrk⟩ := hcot π
  haveI := hfree
  obtain ⟨t, ht, hgen⟩ := P2Body.GenKerAux.exists_generator π hrk
  have hret : ∀ a, π (algA a) = a := fun a => π.commutes a
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have hfg : (RingHom.ker π.toRingHom).FG := SecParam.fg_ker_algHom_stalk c x π
  have ht' : t ∈ RingHom.ker π.toRingHom := ht
  have hgen' : RingHom.ker π.toRingHom ≤ Ideal.span {t} ⊔ RingHom.ker π.toRingHom ^ 2 := by
    simpa [AlgHom.toRingHom_eq_coe] using hgen
  have hI : RingHom.ker π.toRingHom = Ideal.span {t} :=
    SecParam.eq_span_of_le_span_sup_sq hfg (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)) ht' hgen'
  refine ⟨t, hI, ?_⟩
  rw [← hI]
  exact SecParam.maximalIdeal_eq_ker_sup_map algA π.toRingHom hret

end S_AlgebraicGeometry_exists_ker_eq_span_and_maximalIdeal_eq_of_algHom_stalk_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ker_eq_span_and_maximalIdeal_eq_of_algHom_stalk_of_smoothOfRelativeDimension_one (solution)
