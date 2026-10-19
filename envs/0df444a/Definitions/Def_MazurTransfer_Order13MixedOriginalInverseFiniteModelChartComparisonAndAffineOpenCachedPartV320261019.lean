-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedOriginalInverseFiniteModelChartComparisonAndAffineOpenCachedPartV320261019
-- name    : MazurTransfer_Order13MixedOriginalInverseFiniteModelChartComparisonAndAffineOpenCachedPartV320261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T06:51:26.957458+00:00
-- url     : https://prove2.me/theorems/395bf3a8-4f08-4ccf-940e-efc76f791f26
-- title:
--   The original ordinary and inverse chart-overlap compatibility, whole inverse finite-model comparison and actual inverse affine open.
-- statement:
--   The original ordinary and inverse chart-overlap compatibility, whole inverse finite-model comparison and actual inverse affine open. Named downstream consumer: The original ordinary single-section affine comparison and actual two-affine cover.
-- source:
--   MazurTheorem original mixed quadratic affine complements and finite scheme comparisons, by Vas and contributors; original per-file Apache-2.0 attribution retained. Exact official Anthropic FLT source pin 6e837e75355538c7f80bab5b956861e86c4eacc2.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: The original ordinary and inverse chart-overlap compatibility, whole inverse finite-model comparison and actual inverse affine open.
Named downstream consumer: The original ordinary single-section affine comparison and actual two-affine cover.
Original per-file attribution is retained below.
-/
import Definitions.Def_MazurTransfer_Order13MixedOriginalPositiveInfinityEvaluationAndActualSectionComplementCachedPartV320261019

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two actual finite-model charts agree as morphisms to
the actual glued curve on their literal common affine source.
Named downstream consumer: global comparison by the two-member open cover.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve Order13MixedQuadraticTransitionHomomorphisms
open Order13MixedActualPositiveInfinityComplement
variable (R : Type u) [CommRing R] [IsDomain R]

omit [IsDomain R] in
theorem ordinaryInfinityChartMap_overlap_factorization :
    Spec.map (CommRingCat.ofHom (ordinaryOverlapToInfinity R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R))) =
        ordinaryInfinityChartMap R := by
  change Spec.map (CommRingCat.ofHom (ordinaryOverlapToInfinity R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R))) =
    Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R)))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact ordinaryOverlapToInfinity_algebraMap R

theorem ordinaryInfinityToReciprocalPatch_overlap_factorization  :
    ordinaryInfinityToReciprocalPatch R ≫ reciprocalPatchInclusion R =
      Spec.map (CommRingCat.ofHom (ordinaryOverlapToInfinity R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom) := by
  change Spec.map (CommRingCat.ofHom
      ((infinityLocalizedInclusion R).comp (recoveredReciprocalPatchEquiv R).toAlgHom).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R) (Order13MixedSingleSectionReciprocalPatch.PatchRing R))) =
      Spec.map (CommRingCat.ofHom (ordinaryOverlapToInfinity R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom)
  rw [← Spec.map_comp,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change infinityLocalizedInclusion R
    (recoveredReciprocalPatch R 
      (algebraMap (reciprocalCoordinateRing R) (Order13MixedSingleSectionReciprocalPatch.PatchRing R) a)) =
    ordinaryOverlapToInfinity R (reciprocalToOrdinaryBase R a)
  rw [recoveredReciprocalPatch_algebraMap]
  exact DFunLike.congr_fun (recovered_reciprocal_ordinary_comparison_square R) a

omit [IsDomain R] in
theorem ordinary_reciprocal_glue_base :
    Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R))) ≫
      ordinaryChartMap R =
    Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom) ≫ reciprocalChartMap R := by
  have he : Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom) =
      Spec.map (CommRingCat.ofHom (reciprocalToOrdinary R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R))) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (reciprocalToOrdinary_algebraMap R a).symm
  let g : Spec (.of (OrdinaryOverlapRing R)) ⟶ Spec (.of (ReciprocalOverlapRing R)) :=
    Spec.map (CommRingCat.ofHom (reciprocalToOrdinary R).toRingHom)
  let j : Spec (.of (ReciprocalOverlapRing R)) ⟶ reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R)))
  let f : Spec (.of (OrdinaryOverlapRing R)) ⟶ reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom)
  have hcomp : f = g ≫ j := he
  have H := Order13MixedQuadraticActualCurveBaseChange.ordinary_reciprocal_glue R
  have he' := congrArg (fun k : Spec (.of (OrdinaryOverlapRing R)) ⟶ reciprocalScheme R =>
    k ≫ reciprocalChartMap R) hcomp
  exact H.trans ((Category.assoc g j (reciprocalChartMap R)).symm.trans he'.symm)

theorem finiteScheme_concrete_overlap_curve_compatibility  :
    ordinaryInfinityChartMap R ≫ ordinaryChartMap R =
      ordinaryInfinityToReciprocalPatch R ≫ reciprocalPatchChartMap R := by
  let k : Spec (.of (ordinaryInfinityLocalization R)) ⟶ Spec (.of (OrdinaryOverlapRing R)) :=
    Spec.map (CommRingCat.ofHom (ordinaryOverlapToInfinity R).toRingHom)
  let i : Spec (.of (OrdinaryOverlapRing R)) ⟶ ordinaryScheme R :=
    Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R)))
  let j : Spec (.of (OrdinaryOverlapRing R)) ⟶ reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom)
  have hf : k ≫ i = ordinaryInfinityChartMap R := ordinaryInfinityChartMap_overlap_factorization R
  have hg : i ≫ ordinaryChartMap R = j ≫ reciprocalChartMap R := ordinary_reciprocal_glue_base R
  have hh : ordinaryInfinityToReciprocalPatch R ≫ reciprocalPatchInclusion R = k ≫ j :=
    ordinaryInfinityToReciprocalPatch_overlap_factorization R
  calc
    _ = (k ≫ i) ≫ ordinaryChartMap R := congrArg
      (fun a : Spec (.of (ordinaryInfinityLocalization R)) ⟶ ordinaryScheme R => a ≫ ordinaryChartMap R) hf.symm
    _ = k ≫ (i ≫ ordinaryChartMap R) := Category.assoc _ _ _
    _ = k ≫ (j ≫ reciprocalChartMap R) := congrArg (fun a => k ≫ a) hg
    _ = (k ≫ j) ≫ reciprocalChartMap R := (Category.assoc _ _ _).symm
    _ = (ordinaryInfinityToReciprocalPatch R ≫ reciprocalPatchInclusion R) ≫ reciprocalChartMap R :=
      congrArg (fun a => a ≫ reciprocalChartMap R) hh.symm
    _ = ordinaryInfinityToReciprocalPatch R ≫ (reciprocalPatchInclusion R ≫ reciprocalChartMap R) :=
      Category.assoc _ _ _
    _ = _ := rfl

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.finiteScheme_concrete_overlap_curve_compatibility

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two actual inverse finite-model charts agree as morphisms to
the actual glued curve on their literal common affine source.
Named downstream consumer: inverse global comparison by the two-member open cover.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve Order13MixedQuadraticTransitionHomomorphisms
open Order13MixedInverseParameterPolynomialIdentities (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R] [IsDomain R]

theorem ordinaryInfinityChartMap_overlap_factorization :
    ordinaryInfinityChartMap R ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R))) =
    Spec.map (CommRingCat.ofHom (ordinaryOverlapToInfinity R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R))) := by
  change Spec.map (CommRingCat.ofHom (algebraMap (ordinaryParameterLocalization R)
      (ordinaryInfinityLocalization R))) ≫ _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (ordinaryOverlapToInfinity_algebraMap R c).symm

theorem ordinaryInfinityToReciprocalPatch_overlap_factorization  :
    ordinaryInfinityToReciprocalPatch R ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (reciprocalCoordinateRing R) (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))) =
      Spec.map (CommRingCat.ofHom (ordinaryOverlapToInfinity R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom) := by
  change Spec.map (CommRingCat.ofHom
      ((infinityLocalizedInclusion R).comp (recoveredReciprocalPatchEquiv R).toAlgHom).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R) (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))) =
      Spec.map (CommRingCat.ofHom (ordinaryOverlapToInfinity R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom)
  rw [← Spec.map_comp,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change infinityLocalizedInclusion R
    (recoveredReciprocalPatch R 
      (algebraMap (reciprocalCoordinateRing R) (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R) a)) =
    ordinaryOverlapToInfinity R (reciprocalToOrdinaryBase R a)
  rw [recoveredReciprocalPatch_algebraMap]
  exact DFunLike.congr_fun (recovered_reciprocal_ordinary_comparison_square R) a

theorem finiteScheme_concrete_overlap_curve_compatibility  :
    ordinaryInfinityChartMap R ≫ ordinaryParameterCurveMap R =
      ordinaryInfinityToReciprocalPatch R ≫ positiveReciprocalCurveMap R := by
  let u : Spec (.of (ordinaryParameterLocalization R)) ⟶ ordinaryScheme R :=
    Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)))
  let k : Spec (.of (ordinaryInfinityLocalization R)) ⟶ Spec (.of (OrdinaryOverlapRing R)) :=
    Spec.map (CommRingCat.ofHom (ordinaryOverlapToInfinity R).toRingHom)
  let i : Spec (.of (OrdinaryOverlapRing R)) ⟶ ordinaryScheme R :=
    Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R)))
  let j : Spec (.of (OrdinaryOverlapRing R)) ⟶ reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom)
  let v : Spec (.of (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) ⟶ reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R)
      (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)))
  have hf : ordinaryInfinityChartMap R ≫ u = k ≫ i := ordinaryInfinityChartMap_overlap_factorization R
  have hg : i ≫ ordinaryChartMap R = j ≫ reciprocalChartMap R :=
    Order13MixedSingleSectionFiniteAlgebra.ordinary_reciprocal_glue_base R
  have hh : ordinaryInfinityToReciprocalPatch R ≫ v = k ≫ j :=
    ordinaryInfinityToReciprocalPatch_overlap_factorization R
  calc
    _ = (ordinaryInfinityChartMap R ≫ u) ≫ ordinaryChartMap R := (Category.assoc _ _ _).symm
    _ = (k ≫ i) ≫ ordinaryChartMap R := congrArg (fun a => a ≫ ordinaryChartMap R) hf
    _ = k ≫ (i ≫ ordinaryChartMap R) := Category.assoc _ _ _
    _ = k ≫ (j ≫ reciprocalChartMap R) := congrArg (fun a => k ≫ a) hg
    _ = (k ≫ j) ≫ reciprocalChartMap R := (Category.assoc _ _ _).symm
    _ = (ordinaryInfinityToReciprocalPatch R ≫ v) ≫ reciprocalChartMap R :=
      congrArg (fun a => a ≫ reciprocalChartMap R) hh.symm
    _ = ordinaryInfinityToReciprocalPatch R ≫ (v ≫ reciprocalChartMap R) := Category.assoc _ _ _
    _ = _ := rfl

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.finiteScheme_concrete_overlap_curve_compatibility

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse finite coordinate scheme maps to the actual
glued curve with exact ordinary and reciprocal restrictions and exact
union-of-chart image. Named downstream consumer: proving this comparison
an open immersion and constructing the inverse affine-open isomorphism.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open CategoryTheory Limits AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve

variable (R : Type u) [CommRing R] [IsDomain R]

theorem finiteScheme_mixed_chart_curve_compatibility  :
    pullback.fst (ordinaryParameterToFiniteAffineScheme R) (reciprocalToFiniteAffineScheme R) ≫
      ordinaryParameterCurveMap R =
    pullback.snd (ordinaryParameterToFiniteAffineScheme R) (reciprocalToFiniteAffineScheme R) ≫
      positiveReciprocalCurveMap R := by
  have h := (ordinaryInfinityOverlap_isPullback R).flip
  apply (cancel_epi h.isoPullback.hom).mp
  simpa only [← Category.assoc,IsPullback.isoPullback_hom_fst,IsPullback.isoPullback_hom_snd]
    using finiteScheme_concrete_overlap_curve_compatibility R

def finiteSchemeChartToCurve : (b : Bool) → finiteSchemeChart R b ⟶ curveScheme R
  | true => ordinaryParameterCurveMap R
  | false => positiveReciprocalCurveMap R

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
      change pullback.fst (reciprocalToFiniteAffineScheme R) (reciprocalToFiniteAffineScheme R) ≫ positiveReciprocalCurveMap R = pullback.snd (reciprocalToFiniteAffineScheme R) (reciprocalToFiniteAffineScheme R) ≫ positiveReciprocalCurveMap R
      rw [he]
    | true =>
      change pullback.fst (reciprocalToFiniteAffineScheme R) (ordinaryParameterToFiniteAffineScheme R) ≫
        positiveReciprocalCurveMap R = pullback.snd (reciprocalToFiniteAffineScheme R)
          (ordinaryParameterToFiniteAffineScheme R) ≫ ordinaryParameterCurveMap R
      apply (cancel_epi (pullbackSymmetry (ordinaryParameterToFiniteAffineScheme R)
        (reciprocalToFiniteAffineScheme R)).hom).mp
      rw [← Category.assoc,← Category.assoc,
        pullbackSymmetry_hom_comp_fst,pullbackSymmetry_hom_comp_snd]
      exact (finiteScheme_mixed_chart_curve_compatibility R).symm
  | true =>
    cases j with
    | false => exact finiteScheme_mixed_chart_curve_compatibility R
    | true =>
      let := ordinaryParameterToFiniteAffineScheme_isOpenImmersion R
      have he : pullback.fst (ordinaryParameterToFiniteAffineScheme R)
          (ordinaryParameterToFiniteAffineScheme R) = pullback.snd _ _ :=
        (cancel_mono (ordinaryParameterToFiniteAffineScheme R)).mp pullback.condition
      change pullback.fst (ordinaryParameterToFiniteAffineScheme R) (ordinaryParameterToFiniteAffineScheme R) ≫ ordinaryParameterCurveMap R = pullback.snd (ordinaryParameterToFiniteAffineScheme R) (ordinaryParameterToFiniteAffineScheme R) ≫ ordinaryParameterCurveMap R
      rw [he]

def finiteModelToCurve  : inverseFiniteAffineScheme R ⟶ curveScheme R :=
  (finiteSchemeOpenCover R).glueMorphisms (finiteSchemeChartToCurve R)
    (finiteScheme_chart_curve_compatibility R)

theorem ordinaryParameterToFiniteAffineScheme_finiteModelToCurve  :
    ordinaryParameterToFiniteAffineScheme R ≫ finiteModelToCurve R = ordinaryParameterCurveMap R :=
  (finiteSchemeOpenCover R).ι_glueMorphisms _ _ true

theorem reciprocalToFiniteAffineScheme_finiteModelToCurve  :
    reciprocalToFiniteAffineScheme R ≫ finiteModelToCurve R = positiveReciprocalCurveMap R :=
  (finiteSchemeOpenCover R).ι_glueMorphisms _ _ false

theorem finiteModelToCurve_range  :
    Set.range (finiteModelToCurve R) =
      Set.range (ordinaryParameterCurveMap R) ∪ Set.range (positiveReciprocalCurveMap R) := by
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    have hp : p ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) ∪
        Set.range (reciprocalToFiniteAffineScheme R) := by
      rw [finiteScheme_two_chart_range_cover]
      trivial
    rcases hp with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · rw [← Scheme.Hom.comp_apply,ordinaryParameterToFiniteAffineScheme_finiteModelToCurve]
      exact Or.inl ⟨a,rfl⟩
    · rw [← Scheme.Hom.comp_apply,reciprocalToFiniteAffineScheme_finiteModelToCurve]
      exact Or.inr ⟨a,rfl⟩
  · rintro (⟨a,rfl⟩ | ⟨a,rfl⟩)
    · refine ⟨ordinaryParameterToFiniteAffineScheme R a,?_⟩
      rw [← Scheme.Hom.comp_apply,ordinaryParameterToFiniteAffineScheme_finiteModelToCurve]
    · refine ⟨reciprocalToFiniteAffineScheme R a,?_⟩
      rw [← Scheme.Hom.comp_apply,reciprocalToFiniteAffineScheme_finiteModelToCurve]


end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.finiteModelToCurve
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.finiteModelToCurve_range

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse finite model is isomorphic to its
literal affine-open image in the original curve.
Named downstream consumer: the second chart of whole single-section
FiniteMapData and the integral Picard representation inputs.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve Order13MixedQuadraticTransitionHomomorphisms
open Order13MixedInverseParameterPolynomialIdentities (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R]

instance ordinaryParameterCurveMap_isOpenImmersion :
    IsOpenImmersion (ordinaryParameterCurveMap R) := by
  let j : Spec (.of (ordinaryParameterLocalization R)) ⟶ ordinaryScheme R :=
    Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)))
  let : IsOpenImmersion j := IsOpenImmersion.of_isLocalization
    (Order13MixedSingleSectionPolynomialIdentities.t R)
  exact IsOpenImmersion.comp j (ordinaryChartMap R)

instance positiveReciprocalCurveMap_isOpenImmersion :
    IsOpenImmersion (positiveReciprocalCurveMap R) := by
  let j : Spec (.of (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) ⟶ reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R)
      (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)))
  let : IsOpenImmersion j := IsOpenImmersion.of_isLocalization
    (Order13MixedInverseParameterPositiveReciprocalPatch.f R * Order13MixedInverseParameterPositiveReciprocalPatch.g R)
  exact IsOpenImmersion.comp j (reciprocalChartMap R)

def inverseChartOpen : (curveScheme R).Opens :=
  (ordinaryParameterCurveMap R).opensRange ⊔ (positiveReciprocalCurveMap R).opensRange

variable [IsDomain R]

theorem reciprocal_finite_mem_ordinary_range_iff 
    (b : PrimeSpectrum (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) :
    reciprocalToFiniteAffineScheme R b ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) ↔
      Order13MixedInverseParameterPositiveReciprocalPatch.z R ∉ b.asIdeal := by
  rw [ordinaryParameterToFiniteAffineScheme_range]
  change b ∈ (reciprocalToFiniteAffineScheme R) ⁻¹ᵁ (PrimeSpectrum.basicOpen (sElement R)) ↔ _
  rw [reciprocalToFiniteAffineScheme_parameter_preimage]
  rfl

omit [IsDomain R] in
theorem reciprocal_curve_mem_original_ordinary_range_iff
    (b : PrimeSpectrum (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) :
    positiveReciprocalCurveMap R b ∈ Set.range (ordinaryChartMap R) ↔
      Order13MixedInverseParameterPositiveReciprocalPatch.z R ∉ b.asIdeal := by
  have he := Set.ext_iff.mp
    (Order13MixedActualTwoChartRangeOverlap.reciprocalChartMap_preimage_ordinary_range R)
      (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R)
        (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))) b)
  exact he

theorem ordinary_reciprocal_points_identified 
    (a : Spec (.of (ordinaryParameterLocalization R)))
    (b : PrimeSpectrum (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))
    (hab : ordinaryParameterCurveMap R a = positiveReciprocalCurveMap R b) :
    ordinaryParameterToFiniteAffineScheme R a = reciprocalToFiniteAffineScheme R b := by
  have hb : positiveReciprocalCurveMap R b ∈ Set.range (ordinaryChartMap R) := ⟨Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R))) a, hab⟩
  have hf : reciprocalToFiniteAffineScheme R b ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) :=
    (reciprocal_finite_mem_ordinary_range_iff R b).mpr
      ((reciprocal_curve_mem_original_ordinary_range_iff R b).mp hb)
  obtain ⟨a',ha'⟩ := hf
  have hv : ordinaryParameterCurveMap R a' = positiveReciprocalCurveMap R b := by
    have hh := congrArg (finiteModelToCurve R) ha'
    change (ordinaryParameterToFiniteAffineScheme R ≫ finiteModelToCurve R) a' =
      (reciprocalToFiniteAffineScheme R ≫ finiteModelToCurve R) b at hh
    rwa [ordinaryParameterToFiniteAffineScheme_finiteModelToCurve,
      reciprocalToFiniteAffineScheme_finiteModelToCurve] at hh
  have haa' : a = a' := (ordinaryParameterCurveMap R).isOpenEmbedding.injective (hab.trans hv.symm)
  rwa [haa']

theorem finiteModelToCurve_injective  :
    Function.Injective (finiteModelToCurve R) := by
  intro p q hpq
  have hp : p ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) ∪
      Set.range (reciprocalToFiniteAffineScheme R) := by
    rw [finiteScheme_two_chart_range_cover];trivial
  have hq : q ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) ∪
      Set.range (reciprocalToFiniteAffineScheme R) := by
    rw [finiteScheme_two_chart_range_cover];trivial
  rcases hp with ⟨a,rfl⟩ | ⟨b,rfl⟩ <;> rcases hq with ⟨a',rfl⟩ | ⟨b',rfl⟩
  · simp only [← Scheme.Hom.comp_apply,ordinaryParameterToFiniteAffineScheme_finiteModelToCurve] at hpq
    exact congrArg (ordinaryParameterToFiniteAffineScheme R) ((ordinaryParameterCurveMap R).isOpenEmbedding.injective hpq)
  · simp only [← Scheme.Hom.comp_apply,ordinaryParameterToFiniteAffineScheme_finiteModelToCurve,
      reciprocalToFiniteAffineScheme_finiteModelToCurve] at hpq
    exact ordinary_reciprocal_points_identified R a b' hpq
  · simp only [← Scheme.Hom.comp_apply,ordinaryParameterToFiniteAffineScheme_finiteModelToCurve,
      reciprocalToFiniteAffineScheme_finiteModelToCurve] at hpq
    exact (ordinary_reciprocal_points_identified R a' b hpq.symm).symm
  · simp only [← Scheme.Hom.comp_apply,reciprocalToFiniteAffineScheme_finiteModelToCurve] at hpq
    exact congrArg (reciprocalToFiniteAffineScheme R)
      ((positiveReciprocalCurveMap R).isOpenEmbedding.injective hpq)

theorem finiteModelToCurve_isOpenImmersion  :
    IsOpenImmersion (finiteModelToCurve R) := by
  apply IsOpenImmersion.of_openCover_source _ (finiteSchemeOpenCover R)
    (finiteModelToCurve_injective R)
  intro b
  cases b with
  | true =>
    change IsOpenImmersion (ordinaryParameterToFiniteAffineScheme R ≫ finiteModelToCurve R)
    rw [ordinaryParameterToFiniteAffineScheme_finiteModelToCurve]
    infer_instance
  | false =>
    change IsOpenImmersion (reciprocalToFiniteAffineScheme R ≫ finiteModelToCurve R)
    rw [reciprocalToFiniteAffineScheme_finiteModelToCurve]
    infer_instance

theorem finiteModelToCurve_opensRange  :
    letI := finiteModelToCurve_isOpenImmersion R
    (finiteModelToCurve R).opensRange = inverseChartOpen R := by
  let := finiteModelToCurve_isOpenImmersion R
  apply SetLike.ext'
  exact finiteModelToCurve_range R

def finiteModelInverseChartIso  :
    inverseFiniteAffineScheme R ≅ (inverseChartOpen R).toScheme := by
  let := finiteModelToCurve_isOpenImmersion R
  exact IsOpenImmersion.isoOfRangeEq (finiteModelToCurve R)
    (inverseChartOpen R).ι (by
      rw [Scheme.Opens.range_ι]
      exact finiteModelToCurve_range R)

theorem finiteModelInverseChartIso_hom_ι  :
    (finiteModelInverseChartIso R).hom ≫ (inverseChartOpen R).ι =
      finiteModelToCurve R := by
  let := finiteModelToCurve_isOpenImmersion R
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (by
    rw [Scheme.Opens.range_ι]
    exact finiteModelToCurve_range R)

theorem finiteModelInverseChartIso_inv_comp  :
    (finiteModelInverseChartIso R).inv ≫ finiteModelToCurve R =
      (inverseChartOpen R).ι := by
  let := finiteModelToCurve_isOpenImmersion R
  exact IsOpenImmersion.isoOfRangeEq_inv_fac _ _ (by
    rw [Scheme.Opens.range_ι]
    exact finiteModelToCurve_range R)

theorem inverseChartOpen_isAffineOpen  :
    IsAffineOpen (inverseChartOpen R) := by
  let : IsAffine (inverseFiniteAffineScheme R) := by
    unfold inverseFiniteAffineScheme
    infer_instance
  exact IsAffine.of_isIso (finiteModelInverseChartIso R).inv

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.finiteModelToCurve_isOpenImmersion
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.finiteModelInverseChartIso

end


