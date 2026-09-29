-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_cotangent_sectionAlgHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/a3978dc4-21f9-5774-bdef-8691530d5428

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_cotangent_sectionAlgHom

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension.smooth Surjective SmoothOfRelativeDimension Spec Scheme Smooth HasRingHomProperty.appLE isAffineOpen_top Smooth.smooth_appLE HasRingHomProperty Scheme.ΓSpecIso Scheme.TwoAffineOpenCover.sectionAlgHom Scheme.TwoAffineOpenCover"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Γ ΓSpecIso TwoAffineOpenCover.sectionAlgHom TwoAffineOpenCover"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "sectionAlgHom cover isAffineOpen_U0 U0"
namespace CotSec
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

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

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.CotSec

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] {X : AlgebraicGeometry.Scheme.{u}}
    {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ AlgebraicGeometry.Spec (.of R)}
    [AlgebraicGeometry.SmoothOfRelativeDimension 1 c]
    (σ : AlgebraicGeometry.Spec (.of R) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (hU : Set.range σ.base ⊆ (𝒱.U0 : Set X)) :
    Module.Free R (RingHom.ker
        (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom σ hσ hU).toRingHom).Cotangent ∧
      Module.finrank R (RingHom.ker
        (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom σ hσ hU).toRingHom).Cotangent = 1 := by
  haveI : AlgebraicGeometry.Smooth c := AlgebraicGeometry.SmoothOfRelativeDimension.smooth 1 c

  haveI : Algebra.FormallySmooth R (𝒱.cover c).A0 := by
    have h1 : (c.appLE ⊤ 𝒱.U0 le_top).hom.FormallySmooth :=
      (AlgebraicGeometry.Smooth.smooth_appLE (f := c)
        (AlgebraicGeometry.isAffineOpen_top (AlgebraicGeometry.Spec (.of R))) 𝒱.isAffineOpen_U0
          le_top).formallySmooth
    have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ 𝒱.U0 le_top).hom.FormallySmooth := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr h1
    exact h2.toAlgebra

  have hloc : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f)
      (algebraMap R (𝒱.cover c).A0) := by
    have h1 : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f)
        (c.appLE ⊤ 𝒱.U0 le_top).hom :=
      AlgebraicGeometry.HasRingHomProperty.appLE (@AlgebraicGeometry.SmoothOfRelativeDimension 1) c
        inferInstance ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ ⟨𝒱.U0, 𝒱.isAffineOpen_U0⟩ le_top
    have h2 : RingHom.Locally (fun f => RingHom.IsStandardSmoothOfRelativeDimension 1 f)
        ((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ 𝒱.U0 le_top).hom := by
      rw [CommRingCat.hom_comp]
      exact ((RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso).cancel_left_isIso
        _ _).mpr h1
    exact h2
  exact AlgebraicGeometry.Scheme.TwoAffineOpenCover.CotSec.free_cotangent_ker _ hloc

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_cotangent_sectionAlgHom
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_cotangent_sectionAlgHom (solution)
