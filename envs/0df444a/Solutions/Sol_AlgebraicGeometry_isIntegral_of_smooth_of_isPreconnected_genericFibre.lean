-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_of_smooth_of_isPreconnected_genericFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a52b242b-fe89-5800-a891-6f039c95e231

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegral_of_smooth_of_isPreconnected_genericFibre

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

namespace G0Proof

theorem range_specMap_eq {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap R K))).base =
      {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := by
  ext p
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, rfl⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) q.asIdeal = ⊥
    have hq : q.asIdeal = ⊥ := by
      haveI := q.isPrime
      exact Ideal.eq_bot_of_prime q.asIdeal
    rw [hq, Ideal.comap_bot_of_injective _ hinj]
  · rintro rfl
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ hinj

theorem dense_preimage_genericPoint {R : Type u} [CommRing R] [IsDomain R] {D : Scheme.{u}}
    (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] :
    Dense (t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}) := by
  intro p
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ⤳ t.base p := by
    rw [← PrimeSpectrum.le_iff_specializes]
    exact bot_le
  obtain ⟨q, hq, htq⟩ := Flat.generalizingMap t hgen
  have hqmem : q ∈ t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := htq
  apply closure_mono (Set.singleton_subset_iff.mpr hqmem)
  exact hq.mem_closure

end G0Proof

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [Smooth g] [QuasiCompact g]
    [Nonempty ↑(pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    (hconn : _root_.IsPreconnected
      (Set.univ : Set ↑(pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K)))))) :
    IsIntegral G := by

  have hdom : ∀ x : G, IsDomain (G.presheaf.stalk x) := fun x =>
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R g x).1
  haveI : ∀ x : G, _root_.IsReduced (G.presheaf.stalk x) := fun x => by
    haveI := hdom x; infer_instance
  haveI : IsReduced G := isReduced_of_isReduced_stalk G

  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian g
  have hopen : ∀ x : G, IsOpen (irreducibleComponent x) := fun x =>
    (AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk hdom x).1

  let bK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let D : Set G := g.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}
  have hD : Dense D := G0Proof.dense_preimage_genericPoint g
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hrange : Set.range (pullback.fst g bK).base = D := by
    change _ = g.base ⁻¹' _
    rw [Scheme.Pullback.range_fst, G0Proof.range_specMap_eq hinj]
  have hDconn : _root_.IsPreconnected D := by
    rw [← hrange, ← Set.image_univ]
    exact hconn.image _ (pullback.fst g bK).base.hom.continuous.continuousOn

  haveI : PreconnectedSpace G := ⟨by
    have := hDconn.closure
    rwa [hD.closure_eq] at this⟩
  have hne : Nonempty G := by
    obtain ⟨p⟩ := (inferInstance : Nonempty ↑(pullback g bK))
    exact ⟨(pullback.fst g bK).base p⟩

  obtain ⟨x⟩ := hne
  have hcomp : irreducibleComponent x = Set.univ :=
    IsClopen.eq_univ ⟨isClosed_irreducibleComponent, hopen x⟩ ⟨x, mem_irreducibleComponent⟩
  haveI : PreirreducibleSpace G := ⟨by rw [← hcomp]; exact isIrreducible_irreducibleComponent.isPreirreducible⟩
  haveI : IrreducibleSpace G := IrreducibleSpace.mk ⟨x⟩

  exact isIntegral_of_irreducibleSpace_of_isReduced G

end S_AlgebraicGeometry_isIntegral_of_smooth_of_isPreconnected_genericFibre
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegral_of_smooth_of_isPreconnected_genericFibre (solution)
