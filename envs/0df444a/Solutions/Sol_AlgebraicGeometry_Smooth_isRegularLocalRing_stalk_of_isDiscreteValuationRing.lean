-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d9b75099-5ecd-5f1b-a2c2-c8964ca73603

import Mathlib
import Theorems.Thm_isRegularLocalRing_localization_atPrime_of_etale_of_comap
import Definitions.Def_Mathlib_RingTheory_KmfloorsFiberPolynomialRegularAscent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Smooth.exists_isStandardSmooth Spec Scheme Smooth HasRingHomProperty.appLE isAffineOpen_top Etale HasRingHomProperty Scheme.ΓSpecIso"
namespace SmoothRegularDVR
p2m_open "AlgebraicGeometry"

theorem isRegularRing_mvPolynomial_fin (R : Type u) [CommRing R] [IsRegularRing R] (n : ℕ) :
    IsRegularRing (MvPolynomial (Fin n) R) := by
  induction n with
  | zero =>
    exact IsRegularRing.of_ringEquiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.toRingEquiv
  | succ n ih =>
    haveI := ih
    haveI : IsRegularRing (Polynomial (MvPolynomial (Fin n) R)) :=
      kmf2_polyasc_isRegularRing_polynomial_of_isRegularRing (MvPolynomial (Fin n) R)
    exact IsRegularRing.of_ringEquiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv

theorem isRegularLocalRing_of_isLocalization_atPrime
    (R : Type u) [CommRing R] [IsRegularRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] (Sₚ : Type u) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization.AtPrime Sₚ p] :
    IsRegularLocalRing Sₚ := by
  classical
  have hp : p.IsPrime := inferInstance

  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R p
  set Sf := Localization.Away f with hSf
  haveI : Algebra.IsStandardSmooth R Sf := hstd

  obtain ⟨ι, σ, hσ, hι, ⟨Pr⟩⟩ := (inferInstance : Algebra.IsStandardSmooth R Sf).out
  haveI : Algebra.IsStandardSmoothOfRelativeDimension Pr.dimension R Sf := ⟨ι, σ, hσ, hι, Pr, rfl⟩
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial Pr.dimension R Sf
  letI : Algebra (MvPolynomial (Fin Pr.dimension) R) Sf := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin Pr.dimension) R) Sf := hg

  have hdisj : Disjoint (Submonoid.powers f : Set S) (p : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  set q : Ideal Sf := p.map (algebraMap S Sf) with hq
  haveI hqp : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) Sf p hp hdisj
  have hcomap : q.comap (algebraMap S Sf) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f) Sf hp hdisj

  have hunit : IsUnit (algebraMap S Sₚ f) := IsLocalization.map_units Sₚ (⟨f, hf⟩ : p.primeCompl)
  letI : Algebra Sf Sₚ := (IsLocalization.Away.lift f hunit).toAlgebra
  haveI : IsScalarTower S Sf Sₚ := IsScalarTower.of_algebraMap_eq fun s => by
    simp [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_eq]
  have hle : Submonoid.powers f ≤ p.primeCompl := by
    rintro _ ⟨k, rfl⟩
    exact fun h => hf (hp.mem_of_pow_mem k h)
  haveI hloc : IsLocalization (p.primeCompl.map (algebraMap S Sf)) Sₚ :=
    IsLocalization.isLocalization_of_submonoid_le Sf Sₚ (Submonoid.powers f) p.primeCompl hle
  haveI : IsLocalization.AtPrime Sₚ q := by
    refine IsLocalization.of_le_of_exists_dvd (p.primeCompl.map (algebraMap S Sf)) q.primeCompl ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      change algebraMap S Sf s ∉ q
      intro h
      exact hs (by rw [← hcomap]; exact h)
    · intro n hn
      obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) n
      have hm : (m : S) ∉ p := Set.disjoint_left.mp hdisj m.2
      have hs : s ∉ p := by
        intro hs
        apply hn
        have hspec : IsLocalization.mk' Sf s m * algebraMap S Sf m = algebraMap S Sf s :=
          IsLocalization.mk'_spec Sf s m
        have hmem : algebraMap S Sf s ∈ q := Ideal.mem_map_of_mem _ hs
        rw [← hspec] at hmem
        rcases hqp.mem_or_mem hmem with h | h
        · exact h
        · exact absurd (show (m : S) ∈ p by rw [← hcomap]; exact h) hm
      exact ⟨algebraMap S Sf s, ⟨s, hs, rfl⟩, algebraMap S Sf m, (IsLocalization.mk'_spec Sf s m).symm⟩

  haveI : IsRegularRing (MvPolynomial (Fin Pr.dimension) R) :=
    isRegularRing_mvPolynomial_fin R Pr.dimension
  have hreg : IsRegularLocalRing (Localization.AtPrime q) :=
    isRegularLocalRing_localization_atPrime_of_etale_of_comap
      (MvPolynomial (Fin Pr.dimension) R) Sf q
      (IsRegularRing.isRegularLocalRing_localization _)
  haveI := hreg
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) Sₚ).toRingEquiv

end AlgebraicGeometry.SmoothRegularDVR

open AlgebraicGeometry.SmoothRegularDVR in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] (x : T) :
    IsRegularLocalRing (T.presheaf.stalk x) := by
  classical
  obtain ⟨U, hU, V, hV, hxV, hle, -⟩ := Smooth.exists_isStandardSmooth (f := t) x
  have hle' : V ≤ t ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := le_top
  have hQ : (t.appLE ⊤ V hle').hom.Smooth :=
    HasRingHomProperty.appLE @Smooth t inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ hle'
  let e : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  let ψ : R →+* Γ(T, V) := (t.appLE ⊤ V hle').hom.comp e.toRingHom
  have hψ : ψ.Smooth := RingHom.Smooth.respectsIso.2 _ e hQ
  letI : Algebra R Γ(T, V) := ψ.toAlgebra
  haveI : Algebra.Smooth R Γ(T, V) := RingHom.smooth_algebraMap.mp hψ
  letI : Algebra Γ(T, V) (T.presheaf.stalk x) := (T.presheaf.germ V x hxV).hom.toAlgebra
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  exact isRegularLocalRing_of_isLocalization_atPrime R Γ(T, V)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal (T.presheaf.stalk x)

end S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing (solution)
