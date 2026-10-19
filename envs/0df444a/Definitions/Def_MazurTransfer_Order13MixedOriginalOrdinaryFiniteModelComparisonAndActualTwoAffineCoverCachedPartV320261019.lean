-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedOriginalOrdinaryFiniteModelComparisonAndActualTwoAffineCoverCachedPartV320261019
-- name    : MazurTransfer_Order13MixedOriginalOrdinaryFiniteModelComparisonAndActualTwoAffineCoverCachedPartV320261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T06:58:50.011321+00:00
-- url     : https://prove2.me/theorems/18906fcd-8897-4e85-87fa-7b7ab76f4a52
-- title:
--   The original ordinary finite-model comparison, its affine section complement, actual two affine charts, their intersection and the same chosen two-affine-cover constructor.
-- statement:
--   The original ordinary finite-model comparison, its affine section complement, actual two affine charts, their intersection and the same chosen two-affine-cover constructor. Named downstream consumer: Actual global-section polynomial bases and whole degree-three FiniteMapData.
-- source:
--   MazurTheorem original mixed quadratic affine complements and finite scheme comparisons, by Vas and contributors; original per-file Apache-2.0 attribution retained. Exact official Anthropic FLT source pin 6e837e75355538c7f80bab5b956861e86c4eacc2.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: The original ordinary finite-model comparison, its affine section complement, actual two affine charts, their intersection and the same chosen two-affine-cover constructor.
Named downstream consumer: Actual global-section polynomial bases and whole degree-three FiniteMapData.
Original per-file attribution is retained below.
-/
import Definitions.Def_MazurTransfer_Order13MixedOriginalInverseFiniteModelChartComparisonAndAffineOpenCachedPartV320261019
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual finite coordinate scheme maps to the actual
glued curve with exact ordinary and reciprocal restrictions and exact
section-complement image. Named downstream consumer: proving this comparison
an open immersion and constructing the affine complement isomorphism.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open CategoryTheory Limits AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
variable (R : Type u) [CommRing R] [IsDomain R]

theorem finiteScheme_mixed_chart_curve_compatibility  :
    pullback.fst (ordinaryToFiniteAffineScheme R) (reciprocalToFiniteAffineScheme R) ≫
      ordinaryChartMap R =
    pullback.snd (ordinaryToFiniteAffineScheme R) (reciprocalToFiniteAffineScheme R) ≫
      reciprocalPatchChartMap R := by
  have h := (ordinaryInfinityOverlap_isPullback R).flip
  apply (cancel_epi h.isoPullback.hom).mp
  simpa only [← Category.assoc,IsPullback.isoPullback_hom_fst,IsPullback.isoPullback_hom_snd]
    using finiteScheme_concrete_overlap_curve_compatibility R

def finiteSchemeChartToCurve : (b : Bool) → finiteSchemeChart R b ⟶ curveScheme R
  | true => ordinaryChartMap R
  | false => reciprocalPatchChartMap R

theorem finiteScheme_chart_curve_compatibility  (i j : Bool) :
    pullback.fst (finiteSchemeChartMap R i) (finiteSchemeChartMap R j) ≫
      finiteSchemeChartToCurve R i =
    pullback.snd (finiteSchemeChartMap R i) (finiteSchemeChartMap R j) ≫
      finiteSchemeChartToCurve R j := by
  cases i with
  | false =>
    cases j with
    | false =>
      let := reciprocalToFiniteAffineScheme_isOpenImmersion R
      have he : pullback.fst (reciprocalToFiniteAffineScheme R)
          (reciprocalToFiniteAffineScheme R) = pullback.snd _ _ :=
        (cancel_mono (reciprocalToFiniteAffineScheme R)).mp pullback.condition
      change pullback.fst (reciprocalToFiniteAffineScheme R) (reciprocalToFiniteAffineScheme R) ≫ reciprocalPatchChartMap R = pullback.snd (reciprocalToFiniteAffineScheme R) (reciprocalToFiniteAffineScheme R) ≫ reciprocalPatchChartMap R
      rw [he]
    | true =>
      change pullback.fst (reciprocalToFiniteAffineScheme R) (ordinaryToFiniteAffineScheme R) ≫
        reciprocalPatchChartMap R = pullback.snd (reciprocalToFiniteAffineScheme R)
          (ordinaryToFiniteAffineScheme R) ≫ ordinaryChartMap R
      apply (cancel_epi (pullbackSymmetry (ordinaryToFiniteAffineScheme R)
        (reciprocalToFiniteAffineScheme R)).hom).mp
      rw [← Category.assoc,← Category.assoc,
        pullbackSymmetry_hom_comp_fst,pullbackSymmetry_hom_comp_snd]
      exact (finiteScheme_mixed_chart_curve_compatibility R).symm
  | true =>
    cases j with
    | false => exact finiteScheme_mixed_chart_curve_compatibility R
    | true =>
      let := ordinaryToFiniteAffineScheme_isOpenImmersion R 
      have he : pullback.fst (ordinaryToFiniteAffineScheme R)
          (ordinaryToFiniteAffineScheme R) = pullback.snd _ _ :=
        (cancel_mono (ordinaryToFiniteAffineScheme R)).mp pullback.condition
      change pullback.fst (ordinaryToFiniteAffineScheme R) (ordinaryToFiniteAffineScheme R) ≫ ordinaryChartMap R = pullback.snd (ordinaryToFiniteAffineScheme R) (ordinaryToFiniteAffineScheme R) ≫ ordinaryChartMap R
      rw [he]

def finiteModelToCurve  : finiteAffineScheme R ⟶ curveScheme R :=
  (finiteSchemeOpenCover R).glueMorphisms (finiteSchemeChartToCurve R)
    (finiteScheme_chart_curve_compatibility R)

theorem ordinaryToFiniteAffineScheme_finiteModelToCurve  :
    ordinaryToFiniteAffineScheme R ≫ finiteModelToCurve R = ordinaryChartMap R :=
  (finiteSchemeOpenCover R).ι_glueMorphisms _ _ true

theorem reciprocalToFiniteAffineScheme_finiteModelToCurve  :
    reciprocalToFiniteAffineScheme R ≫ finiteModelToCurve R = reciprocalPatchChartMap R :=
  (finiteSchemeOpenCover R).ι_glueMorphisms _ _ false

theorem finiteModelToCurve_range  :
    Set.range (finiteModelToCurve R) =
      Set.range (ordinaryChartMap R) ∪ Set.range (reciprocalPatchChartMap R) := by
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    have hp : p ∈ Set.range (ordinaryToFiniteAffineScheme R) ∪
        Set.range (reciprocalToFiniteAffineScheme R) := by
      rw [finiteScheme_two_chart_range_cover]
      trivial
    rcases hp with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · rw [← Scheme.Hom.comp_apply,ordinaryToFiniteAffineScheme_finiteModelToCurve]
      exact Or.inl ⟨a,rfl⟩
    · rw [← Scheme.Hom.comp_apply,reciprocalToFiniteAffineScheme_finiteModelToCurve]
      exact Or.inr ⟨a,rfl⟩
  · rintro (⟨a,rfl⟩ | ⟨a,rfl⟩)
    · refine ⟨ordinaryToFiniteAffineScheme R a,?_⟩
      rw [← Scheme.Hom.comp_apply,ordinaryToFiniteAffineScheme_finiteModelToCurve]
    · refine ⟨reciprocalToFiniteAffineScheme R a,?_⟩
      rw [← Scheme.Hom.comp_apply,reciprocalToFiniteAffineScheme_finiteModelToCurve]

theorem finiteModelToCurve_range_eq_section_complement  :
    Set.range (finiteModelToCurve R) =
      (Set.range (Order13MixedQuadraticInfinitySections.infinitySectionZero R))ᶜ := by
  rw [finiteModelToCurve_range]
  exact sectionComplementOpen_eq_section_image_complement R

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.finiteModelToCurve
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.finiteModelToCurve_range_eq_section_complement

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual finite coordinate scheme is isomorphic to the
exact complement of the positive infinity section. Named downstream
consumer: the single-section finite-map and integral Picard packages.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
variable (R : Type u) [CommRing R] [IsDomain R]

def candidateToReciprocalPatch  : candidateAlgebra R →ₐ[R]
    Order13MixedSingleSectionReciprocalPatch.PatchRing R :=
  (recoveredReciprocalPatchEquiv R).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R (candidateAlgebra R) (infinityLocalization R))

theorem candidateToReciprocalPatch_parameter  :
    candidateToReciprocalPatch R (parameterElement R) =
      Order13MixedSingleSectionReciprocalPatch.tau R := by
  apply (recoveredReciprocalPatchEquiv R).injective
  change (recoveredReciprocalPatchEquiv R)
    ((recoveredReciprocalPatchEquiv R).symm (infinityParameter R)) = _
  rw [AlgEquiv.apply_symm_apply,recoveredReciprocalPatchEquiv_tau]

theorem candidateToReciprocalPatch_p  :
    candidateToReciprocalPatch R (pElement R) =
      Order13MixedSingleSectionReciprocalPatch.mu R := by
  apply (recoveredReciprocalPatchEquiv R).injective
  change (recoveredReciprocalPatchEquiv R)
    ((recoveredReciprocalPatchEquiv R).symm (infinityP R)) = _
  rw [AlgEquiv.apply_symm_apply,recoveredReciprocalPatchEquiv_mu]

theorem reciprocal_finite_mem_ordinary_range_iff 
    (b : PrimeSpectrum (Order13MixedSingleSectionReciprocalPatch.PatchRing R)) :
    reciprocalToFiniteAffineScheme R b ∈ Set.range (ordinaryToFiniteAffineScheme R) ↔
      Order13MixedSingleSectionReciprocalPatch.z R ∉ b.asIdeal := by
  rw [ordinaryToFiniteAffineScheme_range R ]
  change candidateToReciprocalPatch R (parameterElement R) ∉ b.asIdeal ∨
      candidateToReciprocalPatch R (pElement R + 1) ∉ b.asIdeal ↔ _
  rw [candidateToReciprocalPatch_parameter,map_add,map_one,candidateToReciprocalPatch_p]
  open Order13MixedSingleSectionReciprocalPatch in
    have ht := tau_eq_z_mul_mu R
  open Order13MixedSingleSectionReciprocalPatch in
    have hq := z_mul_nu R
  have hm : Order13MixedSingleSectionReciprocalPatch.mu R ∉ b.asIdeal := by
    intro h
    exact b.isPrime.ne_top (b.asIdeal.eq_top_of_isUnit_mem h
      (Order13MixedSingleSectionReciprocalPatch.mu_isUnit R ))
  constructor
  · rintro (h | h) hz
    · rw [ht] at h
      exact h (b.asIdeal.mul_mem_right _ hz)
    · rw [← hq] at h
      exact h (b.asIdeal.mul_mem_right _ hz)
  · intro hz
    left
    rw [ht]
    intro h
    exact (b.isPrime.mem_or_mem h).elim hz hm

theorem reciprocal_curve_mem_ordinary_range_iff
    (b : PrimeSpectrum (Order13MixedSingleSectionReciprocalPatch.PatchRing R)) :
    reciprocalPatchChartMap R b ∈ Set.range (ordinaryChartMap R) ↔
      Order13MixedSingleSectionReciprocalPatch.z R ∉ b.asIdeal := by
  have he := Set.ext_iff.mp
    (Order13MixedActualTwoChartRangeOverlap.reciprocalChartMap_preimage_ordinary_range R)
      (reciprocalPatchInclusion R b)
  exact he

theorem ordinary_reciprocal_points_identified 
    (a : Order13DyadicMixedQuadraticCharts.ordinaryScheme R)
    (b : PrimeSpectrum (Order13MixedSingleSectionReciprocalPatch.PatchRing R))
    (hab : ordinaryChartMap R a = reciprocalPatchChartMap R b) :
    ordinaryToFiniteAffineScheme R a = reciprocalToFiniteAffineScheme R b := by
  have hb : reciprocalPatchChartMap R b ∈ Set.range (ordinaryChartMap R) := ⟨a,hab⟩
  have hf : reciprocalToFiniteAffineScheme R b ∈ Set.range (ordinaryToFiniteAffineScheme R) :=
    (reciprocal_finite_mem_ordinary_range_iff R b).mpr
      ((reciprocal_curve_mem_ordinary_range_iff R b).mp hb)
  obtain ⟨a',ha'⟩ := hf
  have hv : ordinaryChartMap R a' = reciprocalPatchChartMap R b := by
    have hh := congrArg (finiteModelToCurve R) ha'
    change (ordinaryToFiniteAffineScheme R ≫ finiteModelToCurve R) a' =
      (reciprocalToFiniteAffineScheme R ≫ finiteModelToCurve R) b at hh
    rwa [ordinaryToFiniteAffineScheme_finiteModelToCurve,
      reciprocalToFiniteAffineScheme_finiteModelToCurve] at hh
  have haa' : a = a' := (ordinaryChartMap R).isOpenEmbedding.injective (hab.trans hv.symm)
  rwa [haa']

theorem finiteModelToCurve_injective  :
    Function.Injective (finiteModelToCurve R) := by
  intro p q hpq
  have hp : p ∈ Set.range (ordinaryToFiniteAffineScheme R) ∪
      Set.range (reciprocalToFiniteAffineScheme R) := by
    rw [finiteScheme_two_chart_range_cover];trivial
  have hq : q ∈ Set.range (ordinaryToFiniteAffineScheme R) ∪
      Set.range (reciprocalToFiniteAffineScheme R) := by
    rw [finiteScheme_two_chart_range_cover];trivial
  rcases hp with ⟨a,rfl⟩ | ⟨b,rfl⟩ <;> rcases hq with ⟨a',rfl⟩ | ⟨b',rfl⟩
  · simp only [← Scheme.Hom.comp_apply,ordinaryToFiniteAffineScheme_finiteModelToCurve] at hpq
    exact congrArg (ordinaryToFiniteAffineScheme R) ((ordinaryChartMap R).isOpenEmbedding.injective hpq)
  · simp only [← Scheme.Hom.comp_apply,ordinaryToFiniteAffineScheme_finiteModelToCurve,
      reciprocalToFiniteAffineScheme_finiteModelToCurve] at hpq
    exact ordinary_reciprocal_points_identified R a b' hpq
  · simp only [← Scheme.Hom.comp_apply,ordinaryToFiniteAffineScheme_finiteModelToCurve,
      reciprocalToFiniteAffineScheme_finiteModelToCurve] at hpq
    exact (ordinary_reciprocal_points_identified R a' b hpq.symm).symm
  · simp only [← Scheme.Hom.comp_apply,reciprocalToFiniteAffineScheme_finiteModelToCurve] at hpq
    exact congrArg (reciprocalToFiniteAffineScheme R)
      ((reciprocalPatchChartMap R).isOpenEmbedding.injective hpq)

theorem finiteModelToCurve_isOpenImmersion  :
    IsOpenImmersion (finiteModelToCurve R) := by
  apply IsOpenImmersion.of_openCover_source _ (finiteSchemeOpenCover R)
    (finiteModelToCurve_injective R)
  intro b
  cases b with
  | true =>
    change IsOpenImmersion (ordinaryToFiniteAffineScheme R ≫ finiteModelToCurve R)
    rw [ordinaryToFiniteAffineScheme_finiteModelToCurve]
    infer_instance
  | false =>
    change IsOpenImmersion (reciprocalToFiniteAffineScheme R ≫ finiteModelToCurve R)
    rw [reciprocalToFiniteAffineScheme_finiteModelToCurve]
    infer_instance

theorem finiteModelToCurve_opensRange  :
    letI := finiteModelToCurve_isOpenImmersion R
    (finiteModelToCurve R).opensRange = sectionComplementOpen R := by
  let := finiteModelToCurve_isOpenImmersion R
  apply SetLike.ext'
  exact finiteModelToCurve_range R

def finiteModelSectionComplementIso  :
    finiteAffineScheme R ≅ (sectionComplementOpen R).toScheme := by
  let := finiteModelToCurve_isOpenImmersion R
  exact IsOpenImmersion.isoOfRangeEq (finiteModelToCurve R)
    (sectionComplementOpen R).ι (by
      rw [Scheme.Opens.range_ι]
      exact finiteModelToCurve_range R)

theorem finiteModelSectionComplementIso_hom_ι  :
    (finiteModelSectionComplementIso R).hom ≫ (sectionComplementOpen R).ι =
      finiteModelToCurve R := by
  let := finiteModelToCurve_isOpenImmersion R
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (by
    rw [Scheme.Opens.range_ι]
    exact finiteModelToCurve_range R)

theorem finiteModelSectionComplementIso_inv_comp  :
    (finiteModelSectionComplementIso R).inv ≫ finiteModelToCurve R =
      (sectionComplementOpen R).ι := by
  let := finiteModelToCurve_isOpenImmersion R
  exact IsOpenImmersion.isoOfRangeEq_inv_fac _ _ (by
    rw [Scheme.Opens.range_ι]
    exact finiteModelToCurve_range R)

theorem sectionComplementOpen_isAffineOpen  :
    IsAffineOpen (sectionComplementOpen R) := by
  letI : IsAffine (finiteAffineScheme R) := by
    unfold finiteAffineScheme
    infer_instance
  exact IsAffine.of_isIso (finiteModelSectionComplementIso R).inv

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.finiteModelToCurve_isOpenImmersion
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.finiteModelSectionComplementIso

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual first section complement and the actual inverse
finite-chart image are affine opens covering the original whole curve.
Named downstream consumer: whole single-section FiniteMapData and the
original official FLT Picard representation's two-affine-cover input.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionTwoActualAffineCharts
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
open Order13MixedInverseParameterFiniteAlgebra
variable (R : Type u) [CommRing R] [IsDomain R]

theorem positiveInfinitySection_range_subset_inverseChart  :
    Set.range (Order13MixedQuadraticInfinitySections.infinitySectionZero R) ⊆
      (inverseChartOpen R : Set (curveScheme R)) := by
  rintro p ⟨a,rfl⟩
  right
  refine ⟨positiveInfinityPatchMorphism R a, ?_⟩
  have he := positiveInfinityPatchMorphism_curve R
  exact congrArg (fun f : Spec (.of R) ⟶ curveScheme R => f a) he

theorem actual_two_affine_open_cover  :
    sectionComplementOpen R ⊔ inverseChartOpen R = ⊤ := by
  apply TopologicalSpace.Opens.ext
  ext p
  change (p ∈ sectionComplementOpen R ∨ p ∈ inverseChartOpen R) ↔ True
  constructor
  · intro _; trivial
  · intro _
    by_cases hp : p ∈ Set.range (Order13MixedQuadraticInfinitySections.infinitySectionZero R)
    · exact Or.inr (positiveInfinitySection_range_subset_inverseChart R  hp)
    · left
      rw [← SetLike.mem_coe, sectionComplementOpen_eq_section_image_complement]
      exact hp

theorem actual_first_chart_isAffineOpen  :
    IsAffineOpen (sectionComplementOpen R) :=
  Order13MixedSingleSectionFiniteAlgebra.sectionComplementOpen_isAffineOpen R

theorem actual_inverse_chart_isAffineOpen  :
    IsAffineOpen (inverseChartOpen R) := inverseChartOpen_isAffineOpen R

end MazurTransfer.Order13MixedSingleSectionTwoActualAffineCharts
#print axioms MazurTransfer.Order13MixedSingleSectionTwoActualAffineCharts.actual_two_affine_open_cover
#print axioms MazurTransfer.Order13MixedSingleSectionTwoActualAffineCharts.actual_inverse_chart_isAffineOpen

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the first section complement and inverse finite-chart
image meet exactly in the actual ordinary t-open chart.
Named downstream consumer: the overlap and reciprocal-parameter fields of
whole single-section FiniteMapData and the original two-affine-open cover.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement (sectionComplementOpen)
variable (R : Type u) [CommRing R]

open Order13MixedInverseParameterPositiveReciprocalPatch in
theorem positive_patch_z_mem_forces_w_zero (p : PrimeSpectrum (PatchRing R))
    (hz : z R ∈ p.asIdeal) : w R ∈ p.asIdeal := by
  have he : F R * (F R - 1) = z R *
      ((1 + z R ^ 2) * F R + z R ^ 3 * (1 + z R)) := by
    linear_combination F_equation R
  have hf : F R ∉ p.asIdeal := by
    intro h
    have hu : IsUnit (F R) := isUnit_of_mul_isUnit_left
      (show IsUnit (F R * r R) by rw [F_mul_r]; exact isUnit_one)
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h hu)
  have hprod : F R * (F R - 1) ∈ p.asIdeal := by
    rw [he]
    exact p.asIdeal.mul_mem_right _ hz
  have hw := (p.isPrime.mem_or_mem hprod).resolve_left hf
  have hz3 : z R ^ 3 ∈ p.asIdeal := p.asIdeal.pow_mem_of_mem hz 3 (by decide)
  have h := p.asIdeal.sub_mem (p.asIdeal.sub_mem hw hz) hz3
  have hF : F R = w R + (1 + z R + z R ^ 3) := by
    simp only [F, f, w, z, map_add, map_pow, map_one]
  have hval : F R - 1 - z R - z R ^ 3 = w R := by rw [hF]; ring
  rwa [hval] at h

theorem positiveReciprocalCurveMap_mem_sectionComplement_iff
    (p : PrimeSpectrum (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) :
    positiveReciprocalCurveMap R p ∈ sectionComplementOpen R ↔
      Order13MixedInverseParameterPositiveReciprocalPatch.z R ∉ p.asIdeal := by
  have he := Set.ext_iff.mp
    (Order13MixedActualPositiveInfinityComplement.reciprocal_preimage_complement_open R)
      (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R)
        (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))) p)
  have hmem : (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R)
        (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))) p) ∈
      Set.range (Order13MixedPositiveInfinityReciprocalImage.evaluationSchemeMap R) ↔
    Order13MixedInverseParameterPositiveReciprocalPatch.z R ∈ p.asIdeal ∧
      Order13MixedInverseParameterPositiveReciprocalPatch.w R ∈ p.asIdeal := by
    have h := Order13MixedPositiveInfinityReciprocalImage.mem_evaluationSchemeMap_range R
      (PrimeSpectrum.comap (algebraMap (reciprocalCoordinateRing R)
        (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) p)
    change (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R)
        (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))) p) ∈
      Set.range (Order13MixedPositiveInfinityReciprocalImage.evaluationSchemeMap R) ↔
      algebraMap (reciprocalCoordinateRing R) (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)
        (zCoordinate R) ∈ p.asIdeal ∧
      algebraMap (reciprocalCoordinateRing R) (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)
        (wCoordinate R) ∈ p.asIdeal at h
    simpa only [Order13MixedInverseParameterPositiveReciprocalPatch.z,
      Order13MixedInverseParameterPositiveReciprocalPatch.w, map_sub, map_one] using h
  constructor
  · intro hp hz
    exact he.mp hp (hmem.mpr ⟨hz, positive_patch_z_mem_forces_w_zero R p hz⟩)
  · intro hz
    apply he.mpr
    exact fun h => hz (hmem.mp h).1

variable [IsDomain R]

theorem actual_chart_intersection_opensRange  :
    sectionComplementOpen R ⊓ inverseChartOpen R = (ordinaryParameterCurveMap R).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext p
  constructor
  · rintro ⟨hpU, hpV⟩
    rcases hpV with ⟨a,rfl⟩ | ⟨b,rfl⟩
    · exact ⟨a,rfl⟩
    · have hz := (positiveReciprocalCurveMap_mem_sectionComplement_iff R b).mp hpU
      have hb := (reciprocal_finite_mem_ordinary_range_iff R b).mpr hz
      obtain ⟨a,ha⟩ := hb
      refine ⟨a,?_⟩
      have hc := congrArg (finiteModelToCurve R) ha
      change (ordinaryParameterToFiniteAffineScheme R ≫ finiteModelToCurve R) a =
        (reciprocalToFiniteAffineScheme R ≫ finiteModelToCurve R) b at hc
      rwa [ordinaryParameterToFiniteAffineScheme_finiteModelToCurve,
        reciprocalToFiniteAffineScheme_finiteModelToCurve] at hc
  · rintro ⟨a,rfl⟩
    constructor
    · exact Order13MixedActualPositiveInfinityComplement.ordinary_chart_mem_complement_open R
        (Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R)
          (Order13MixedInverseParameterPolynomialIdentities.ordinaryParameterLocalization R))) a)
    · left
      exact ⟨a,rfl⟩

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.positiveReciprocalCurveMap_mem_sectionComplement_iff
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.actual_chart_intersection_opensRange

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual two-affine-open-cover structure on the original
curve, with the distinguished positive infinity section retained.
Named downstream consumer: the original official FLT Picard representation
and whole single-section FiniteMapData.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionActualTwoAffineCover
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
open Order13MixedInverseParameterFiniteAlgebra
variable (R : Type u) [CommRing R] [IsDomain R]

def actualTwoAffineOpenCover  : (curveScheme R).TwoAffineOpenCover where
  U0 := inverseChartOpen R
  U1 := sectionComplementOpen R
  isAffineOpen_U0 := inverseChartOpen_isAffineOpen R
  isAffineOpen_U1 := Order13MixedSingleSectionFiniteAlgebra.sectionComplementOpen_isAffineOpen R
  sup_eq_top := by
    rw [sup_comm]
    exact Order13MixedSingleSectionTwoActualAffineCharts.actual_two_affine_open_cover R
  isAffineOpen_inf := by
    rw [inf_comm, actual_chart_intersection_opensRange R]
    exact isAffineOpen_opensRange (ordinaryParameterCurveMap R)

theorem actualTwoAffineOpenCover_section_range  :
    Set.range (Order13MixedQuadraticInfinitySections.infinitySectionZero R) ⊆
      ((actualTwoAffineOpenCover R).U0 : Set (curveScheme R)) :=
  Order13MixedSingleSectionTwoActualAffineCharts.positiveInfinitySection_range_subset_inverseChart R
    

theorem actualTwoAffineOpenCover_complement  :
    ((actualTwoAffineOpenCover R).U1 : Set (curveScheme R)) =
      (Set.range (Order13MixedQuadraticInfinitySections.infinitySectionZero R))ᶜ :=
  sectionComplementOpen_eq_section_image_complement R

end MazurTransfer.Order13MixedSingleSectionActualTwoAffineCover
#print axioms MazurTransfer.Order13MixedSingleSectionActualTwoAffineCover.actualTwoAffineOpenCover
#print axioms MazurTransfer.Order13MixedSingleSectionActualTwoAffineCover.actualTwoAffineOpenCover_section_range

end


