-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_pullback_and_exists_generic_closedFibre_of_isLocalization_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fcb69f71-a8d4-56b1-941b-18b5a37f00a8

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_isPreconnected_genericFibre
import Theorems.Thm_AlgebraicGeometry_exists_specializes_closedFibre_of_smooth_of_isPreconnected
import Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegral_pullback_and_exists_generic_closedFibre_of_isLocalization_atPrime
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (p : ℕ) [Fact p.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [(Ideal.span {(p : ℤ)}).IsPrime] [IsLocalization.AtPrime R (Ideal.span {(p : ℤ)})]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [Smooth g] [QuasiCompact g]
    (hpre : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (g.base ⁻¹' {s}))

    (e : Spec (CommRingCat.of ℤ) ⟶ G) (he : e ≫ g = 𝟙 (Spec (CommRingCat.of ℤ))) :
    ∃ (_ : IsIntegral (pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))))
      (η : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))),
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base η = IsLocalRing.closedPoint R ∧
      (∀ x : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))),
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base x = IsLocalRing.closedPoint R →
          η ⤳ x) ∧
      (∀ y : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))), y ⤳ η →
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base y = IsLocalRing.closedPoint R →
          y = η) ∧
      IsDiscreteValuationRing ((pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).presheaf.stalk η) := by
  classical
  set ιR := Spec.map (CommRingCat.ofHom (algebraMap ℤ R)) with hιR
  haveI : IsPreimmersion ιR := IsPreimmersion.of_isLocalization (Ideal.span {(p : ℤ)}).primeCompl
  have hemb : Topology.IsEmbedding (pullback.fst g ιR).base := (pullback.fst g ιR).isEmbedding

  have hc : ∀ y : ↥(pullback g ιR), g.base ((pullback.fst g ιR).base y) = ιR.base ((pullback.snd g ιR).base y) := by
    intro y
    have := congrArg (fun k : pullback g ιR ⟶ Spec (CommRingCat.of ℤ) => k.base y) (pullback.condition (f := g) (g := ιR))
    simpa [Scheme.Hom.comp_base, TopCat.comp_app] using this

  have hfib : ∀ s : ↥(Spec (CommRingCat.of R)),
      (pullback.fst g ιR).base '' {y | (pullback.snd g ιR).base y = s} = g.base ⁻¹' {ιR.base s} := by
    intro s
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show g.base ((pullback.fst g ιR).base y) ∈ ({ιR.base s} : Set _)
      rw [Set.mem_singleton_iff, hc y, hy]
    · intro hx
      obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := ιR) x s hx
      exact ⟨z, hz2, hz1⟩
  have hpre' : ∀ s : ↥(Spec (CommRingCat.of R)),
      _root_.IsPreconnected {y : ↥(pullback g ιR) | (pullback.snd g ιR).base y = s} := fun s =>
    (hemb.isInducing.isPreconnected_image).mp (by rw [hfib]; exact hpre _)

  have hge : ∀ t : ↥(Spec (CommRingCat.of ℤ)), g.base (e.base t) = t := by
    intro t
    have := congrArg (fun k : Spec (CommRingCat.of ℤ) ⟶ Spec (CommRingCat.of ℤ) => k.base t) he
    simpa [Scheme.Hom.comp_base, TopCat.comp_app] using this
  have hsec : ∀ s : ↥(Spec (CommRingCat.of R)), ∃ y : ↥(pullback g ιR), (pullback.snd g ιR).base y = s := by
    intro s
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := ιR) (e.base (ιR.base s)) s
      (hge _)
    exact ⟨z, hz⟩

  obtain ⟨η, hη, hirr, hgen⟩ :=
    exists_specializes_closedFibre_of_smooth_of_isPreconnected (pullback.snd g ιR) (hsec _) (hpre' _)

  set ιK := Spec.map (CommRingCat.ofHom (algebraMap R ℚ)) with hιK
  haveI : IsPreimmersion ιK := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hKpt : ∀ q : ↥(Spec (CommRingCat.of ℚ)), ιK.base q = (⊥ : PrimeSpectrum R) := by
    intro q
    apply PrimeSpectrum.ext
    have hq : q = (⊥ : PrimeSpectrum ℚ) := @Subsingleton.elim (PrimeSpectrum ℚ) inferInstance _ _
    subst hq
    change Ideal.comap (algebraMap R ℚ) ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R ℚ)
  have hrangeK : Set.range (pullback.fst (pullback.snd g ιR) ιK).base =
      {y | (pullback.snd g ιR).base y = (⊥ : PrimeSpectrum R)} := by
    rw [Scheme.Pullback.range_fst]
    ext y
    simp only [Set.mem_preimage, Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q, hq⟩; rw [← hq, hKpt]
    · intro hy; exact ⟨(⊥ : PrimeSpectrum ℚ), by rw [hKpt]; exact hy.symm⟩
  haveI : Nonempty ↥(pullback (pullback.snd g ιR) ιK) := by
    obtain ⟨y, hy⟩ := hsec (⊥ : PrimeSpectrum R)
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd g ιR) (g := ιK) y (⊥ : PrimeSpectrum ℚ)
      (by rw [hy, hKpt])
    exact ⟨z⟩
  have hconnK : _root_.IsPreconnected (Set.univ : Set ↥(pullback (pullback.snd g ιR) ιK)) := by
    have hembK : Topology.IsEmbedding (pullback.fst (pullback.snd g ιR) ιK).base :=
      (pullback.fst (pullback.snd g ιR) ιK).isEmbedding
    rw [← hembK.isInducing.isPreconnected_image, Set.image_univ, hrangeK]
    exact hpre' _
  have hint : IsIntegral (pullback g ιR) :=
    isIntegral_of_smooth_of_isPreconnected_genericFibre ℚ (pullback.snd g ιR) hconnK
  obtain ⟨_, hdvr⟩ :=
    Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R (pullback.snd g ιR) η hη hgen
  exact ⟨hint, η, hη, hirr, hgen, hdvr⟩

end S_AlgebraicGeometry_isIntegral_pullback_and_exists_generic_closedFibre_of_isLocalization_atPrime
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegral_pullback_and_exists_generic_closedFibre_of_isLocalization_atPrime (solution)
