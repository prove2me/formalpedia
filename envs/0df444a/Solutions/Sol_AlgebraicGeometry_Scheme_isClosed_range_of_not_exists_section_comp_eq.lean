-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isClosed_range_of_not_exists_section_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f8d0f1c6-1708-5898-be05-55311fa967ac

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_section_comp_eq_of_exists_mem_closure_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_isClosed_range_of_not_exists_section_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (hns : ¬ ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = x) :
    IsClosed (Set.range x.base) := by
  classical
  set ιK := Spec.map (CommRingCat.ofHom (algebraMap R K)) with hιK

  have hmiss : ∀ z ∈ closure (Set.range x.base), f.base z ≠ IsLocalRing.closedPoint R := by
    intro z hz hfz
    exact hns (AlgebraicGeometry.Scheme.exists_section_comp_eq_of_exists_mem_closure_range K f x hx ⟨z, hz, hfz⟩)

  have hgenpt : ∀ q : PrimeSpectrum R, q ≠ IsLocalRing.closedPoint R → q = ⟨⊥, Ideal.isPrime_bot⟩ := by
    intro q hq
    apply PrimeSpectrum.ext
    by_contra hne
    apply hq
    apply PrimeSpectrum.ext
    haveI := q.isPrime
    exact (IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne))
  have hιKpt : ∀ p : ↥(Spec (CommRingCat.of K)), ιK.base p = ⟨⊥, Ideal.isPrime_bot⟩ := by
    intro p
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) p.asIdeal = ⊥
    haveI := p.isPrime
    rw [Ideal.eq_bot_of_prime p.asIdeal, Ideal.comap_bot_of_injective (algebraMap R K) (IsFractionRing.injective R K)]
  have hsub : closure (Set.range x.base) ⊆ Set.range (pullback.fst f ιK).base := by
    intro z hz
    rw [Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint K, ?_⟩
    rw [hιKpt, ← hgenpt _ (hmiss z hz)]

  let xK : Spec (CommRingCat.of K) ⟶ pullback f ιK := pullback.lift x (𝟙 _) (by rw [hx, Category.id_comp])
  have hxK : xK ≫ pullback.snd f ιK = 𝟙 _ := pullback.lift_snd _ _ _
  have hxK1 : xK ≫ pullback.fst f ιK = x := pullback.lift_fst _ _ _
  haveI : IsClosedImmersion xK := isClosedImmersion_of_comp_eq_id (pullback.snd f ιK) xK hxK
  have hcl : IsClosed (Set.range xK.base) := xK.isClosedEmbedding.isClosed_range

  haveI : IsPreimmersion ιK := by
    rw [hιK]; exact IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hemb : Topology.IsEmbedding (pullback.fst f ιK).base := (pullback.fst f ιK).isEmbedding
  have hxr : Set.range x.base = (pullback.fst f ιK).base '' Set.range xK.base := by
    rw [← Set.range_comp, ← hxK1]; rfl
  apply isClosed_of_closure_subset
  intro z hz
  obtain ⟨w, rfl⟩ := hsub hz
  have hw : w ∈ (pullback.fst f ιK).base ⁻¹' closure ((pullback.fst f ιK).base '' Set.range xK.base) := by
    rw [← hxr]; exact hz
  rw [← hemb.closure_eq_preimage_closure_image, hcl.closure_eq] at hw
  rw [hxr]
  exact ⟨w, hw, rfl⟩

end S_AlgebraicGeometry_Scheme_isClosed_range_of_not_exists_section_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_isClosed_range_of_not_exists_section_comp_eq (solution)
