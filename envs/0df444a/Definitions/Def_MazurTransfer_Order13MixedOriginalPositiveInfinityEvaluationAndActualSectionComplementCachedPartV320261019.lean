-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedOriginalPositiveInfinityEvaluationAndActualSectionComplementCachedPartV320261019
-- name    : MazurTransfer_Order13MixedOriginalPositiveInfinityEvaluationAndActualSectionComplementCachedPartV320261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T06:47:57.60387+00:00
-- url     : https://prove2.me/theorems/d91e759d-cd72-466e-9ccb-93b8337fb134
-- title:
--   The original positive infinity evaluation kernel, reciprocal section image and actual whole-curve section complement.
-- statement:
--   The original positive infinity evaluation kernel, reciprocal section image and actual whole-curve section complement. Named downstream consumer: The original inverse and ordinary finite-model comparison maps.
-- source:
--   MazurTheorem original mixed quadratic affine complements and finite scheme comparisons, by Vas and contributors; original per-file Apache-2.0 attribution retained. Exact official Anthropic FLT source pin 6e837e75355538c7f80bab5b956861e86c4eacc2.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: The original positive infinity evaluation kernel, reciprocal section image and actual whole-curve section complement.
Named downstream consumer: The original inverse and ordinary finite-model comparison maps.
Original per-file attribution is retained below.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13MixedOriginalSingleSectionAndInverseFiniteSchemeAtlasesData20261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact kernel and surjectivity of the actual positive
infinity evaluation in the mixed reciprocal ring over every commutative
ring. Named downstream consumer: the actual section image and complement.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedPositiveInfinityEvaluationKernel
open Polynomial Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticInfinitySections
variable (R : Type u) [CommRing R]

def evaluation : reciprocalCoordinateRing R →+* R := (infinityPointZero R).toRingHom
abbrev evaluationAlgHom : reciprocalCoordinateRing R →ₐ[R] R := infinityPointZero R

theorem evaluation_z : evaluation R (zCoordinate R) = 0 := by
  simp only [evaluation,infinityPointZero,zCoordinate,AdjoinRoot.liftAlgHom_of,aeval_X,
    AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]
theorem evaluation_w : evaluation R (wCoordinate R) = 0 := AdjoinRoot.liftAlgHom_root _ _ _ _

def sectionIdeal : Ideal (reciprocalCoordinateRing R) := Ideal.span {zCoordinate R,wCoordinate R}
def quotientMap : reciprocalCoordinateRing R →ₐ[R] reciprocalCoordinateRing R ⧸ sectionIdeal R :=
  Ideal.Quotient.mkₐ R (sectionIdeal R)

theorem quotientMap_z : quotientMap R (zCoordinate R) = 0 :=
  (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
theorem quotientMap_w : quotientMap R (wCoordinate R) = 0 :=
  (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))

theorem quotientMap_factorization : quotientMap R =
    (Algebra.ofId R (reciprocalCoordinateRing R ⧸ sectionIdeal R)).comp (evaluationAlgHom R) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change quotientMap R (zCoordinate R) =
      algebraMap R (reciprocalCoordinateRing R ⧸ sectionIdeal R) (evaluation R (zCoordinate R))
    rw [quotientMap_z,evaluation_z,map_zero]
  · change quotientMap R (wCoordinate R) =
      algebraMap R (reciprocalCoordinateRing R ⧸ sectionIdeal R) (evaluation R (wCoordinate R))
    rw [quotientMap_w,evaluation_w,map_zero]

theorem sectionIdeal_le_kernel : sectionIdeal R ≤ RingHom.ker (evaluation R) := by
  apply Ideal.span_le.mpr
  intro b hb
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl
  · exact evaluation_z R
  · exact evaluation_w R

theorem evaluation_kernel : RingHom.ker (evaluation R) = sectionIdeal R := by
  apply le_antisymm
  · intro a ha
    change evaluation R a = 0 at ha
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change quotientMap R a = 0
    have h := DFunLike.congr_fun (quotientMap_factorization R) a
    change quotientMap R a = algebraMap R (reciprocalCoordinateRing R ⧸ sectionIdeal R) (evaluation R a) at h
    rw [ha,map_zero] at h
    exact h
  · exact sectionIdeal_le_kernel R

theorem evaluation_surjective : Function.Surjective (evaluation R) := by
  intro r
  exact ⟨algebraMap R (reciprocalCoordinateRing R) r,(infinityPointZero R).commutes r⟩

theorem denominator_mem_ideal_iff (I : Ideal (reciprocalCoordinateRing R))
    (hz : zCoordinate R ∈ I) :
    Order13MixedSingleSectionReciprocalPatch.denominator R ∈ I ↔ wCoordinate R ∈ I := by
  have he : Order13MixedSingleSectionReciprocalPatch.denominator R =
      wCoordinate R + wCoordinate R * zCoordinate R := by
    dsimp only [Order13MixedSingleSectionReciprocalPatch.denominator];ring
  have hm := I.mul_mem_left (wCoordinate R) hz
  rw [he]
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using I.sub_mem h hm
  · intro h
    exact I.add_mem h hm

end MazurTransfer.Order13MixedPositiveInfinityEvaluationKernel
#print axioms MazurTransfer.Order13MixedPositiveInfinityEvaluationKernel.evaluation_kernel
#print axioms MazurTransfer.Order13MixedPositiveInfinityEvaluationKernel.evaluation_surjective
#print axioms MazurTransfer.Order13MixedPositiveInfinityEvaluationKernel.denominator_mem_ideal_iff

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual positive infinity closed image in the reciprocal
chart and its exact principal-open complement. Named downstream consumer:
identification of the positive section complement in the glued curve.
No whole-curve gluing or single-section affine identification is asserted.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedPositiveInfinityReciprocalImage
open CategoryTheory AlgebraicGeometry Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedPositiveInfinityEvaluationKernel
open Order13MixedSingleSectionReciprocalPatch
variable (R : Type u) [CommRing R]

def evaluationSchemeMap : Spec (.of R) ⟶ reciprocalScheme R :=
  Spec.map (CommRingCat.ofHom (evaluation R))

theorem evaluationSchemeMap_isClosedImmersion : IsClosedImmersion (evaluationSchemeMap R) :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (evaluation R)) (evaluation_surjective R)

theorem evaluationSchemeMap_range : Set.range (evaluationSchemeMap R) =
    PrimeSpectrum.zeroLocus (sectionIdeal R : Set (reciprocalCoordinateRing R)) := by
  change Set.range (PrimeSpectrum.comap (evaluation R)) = _
  rw [range_comap_of_surjective R (evaluation R) (evaluation_surjective R),evaluation_kernel]

theorem mem_evaluationSchemeMap_range (p : PrimeSpectrum (reciprocalCoordinateRing R)) :
    p ∈ Set.range (evaluationSchemeMap R) ↔ zCoordinate R ∈ p.asIdeal ∧ wCoordinate R ∈ p.asIdeal := by
  change p ∈ Set.range (PrimeSpectrum.comap (evaluation R)) ↔ _
  have h : Set.range (PrimeSpectrum.comap (evaluation R)) =
      PrimeSpectrum.zeroLocus (sectionIdeal R : Set (reciprocalCoordinateRing R)) := evaluationSchemeMap_range R
  rw [h,sectionIdeal,PrimeSpectrum.zeroLocus_span,PrimeSpectrum.mem_zeroLocus]
  simp only [Set.insert_subset_iff,Set.singleton_subset_iff]
  rfl

theorem evaluationSchemeMap_range_complement :
    (Set.range (evaluationSchemeMap R))ᶜ =
      (PrimeSpectrum.basicOpen (zCoordinate R) ⊔
        PrimeSpectrum.basicOpen (denominator R) : Set (PrimeSpectrum (reciprocalCoordinateRing R))) := by
  change (Set.range (PrimeSpectrum.comap (evaluation R)))ᶜ =
    (PrimeSpectrum.basicOpen (zCoordinate R) : Set (PrimeSpectrum (reciprocalCoordinateRing R))) ∪
      (PrimeSpectrum.basicOpen (denominator R) : Set (PrimeSpectrum (reciprocalCoordinateRing R)))
  ext p
  change ¬ p ∈ Set.range (PrimeSpectrum.comap (evaluation R)) ↔
    zCoordinate R ∉ p.asIdeal ∨ denominator R ∉ p.asIdeal
  have he : p ∈ Set.range (PrimeSpectrum.comap (evaluation R)) ↔
      zCoordinate R ∈ p.asIdeal ∧ wCoordinate R ∈ p.asIdeal :=
    mem_evaluationSchemeMap_range R p
  rw [he]
  by_cases hz : zCoordinate R ∈ p.asIdeal
  · have hd := Order13MixedPositiveInfinityEvaluationKernel.denominator_mem_ideal_iff R p.asIdeal hz
    simp only [hz,true_and,not_true_eq_false,false_or,hd]
  · simp only [hz,false_and,not_false_eq_true,true_or]

end MazurTransfer.Order13MixedPositiveInfinityReciprocalImage
#print axioms MazurTransfer.Order13MixedPositiveInfinityReciprocalImage.evaluationSchemeMap_isClosedImmersion
#print axioms MazurTransfer.Order13MixedPositiveInfinityReciprocalImage.evaluationSchemeMap_range_complement

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: consume the retained exact chart-overlap proof as a set
range identity. Named downstream consumer: the actual positive infinity
complement in the whole two-chart curve. No affine identification is assumed.
Adapts the existing range wrapper to the actual mixed-curve overlap theorem.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedActualTwoChartRangeOverlap
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
variable (R : Type u) [CommRing R]

theorem reciprocalChartMap_preimage_ordinary_range :
    reciprocalChartMap R ⁻¹' Set.range (ordinaryChartMap R) =
      (PrimeSpectrum.basicOpen (zCoordinate R) : Set (PrimeSpectrum (reciprocalCoordinateRing R))) := by
  exact congrArg (fun U : (reciprocalScheme R).Opens => (U : Set (reciprocalScheme R)))
    (Order13MixedQuadraticHyperellipticMap.reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen R)

end MazurTransfer.Order13MixedActualTwoChartRangeOverlap
#print axioms MazurTransfer.Order13MixedActualTwoChartRangeOverlap.reciprocalChartMap_preimage_ordinary_range

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact positive infinity section complement as an actual
open of the retained two-chart curve over every commutative base ring.
Named downstream consumer: gluing Spec B onto the chosen single-section
complement for FiniteMapData. No affine identification is assumed here.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedActualPositiveInfinityComplement
open CategoryTheory AlgebraicGeometry Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve Order13MixedQuadraticInfinitySections
open Order13MixedSingleSectionReciprocalPatch
open Order13MixedPositiveInfinityReciprocalImage
variable (R : Type u) [CommRing R]

def reciprocalPatchInclusion : Spec (.of (PatchRing R)) ⟶ reciprocalScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R) (PatchRing R)))
instance reciprocalPatchInclusion_isOpenImmersion : IsOpenImmersion (reciprocalPatchInclusion R) :=
  IsOpenImmersion.of_isLocalization (denominator R)

def reciprocalPatchChartMap : Spec (.of (PatchRing R)) ⟶ curveScheme R :=
  reciprocalPatchInclusion R ≫ reciprocalChartMap R
instance reciprocalPatchChartMap_isOpenImmersion : IsOpenImmersion (reciprocalPatchChartMap R) :=
  IsOpenImmersion.comp (reciprocalPatchInclusion R) (reciprocalChartMap R)

def sectionComplementOpen : (curveScheme R).Opens :=
  (ordinaryChartMap R).opensRange ⊔ (reciprocalPatchChartMap R).opensRange

theorem reciprocalPatchInclusion_range : Set.range (reciprocalPatchInclusion R) =
    (PrimeSpectrum.basicOpen (denominator R) : Set (PrimeSpectrum (reciprocalCoordinateRing R))) := by
  exact PrimeSpectrum.localization_away_comap_range (PatchRing R) (denominator R)

theorem reciprocalPatchChartMap_range : Set.range (reciprocalPatchChartMap R) =
    reciprocalChartMap R '' (PrimeSpectrum.basicOpen (denominator R) : Set (PrimeSpectrum (reciprocalCoordinateRing R))) := by
  change Set.range (reciprocalChartMap R ∘ reciprocalPatchInclusion R) = _
  rw [Set.range_comp,reciprocalPatchInclusion_range]

theorem reciprocal_preimage_section_image : reciprocalChartMap R ⁻¹'
    Set.range (infinitySectionZero R) =
      Set.range (evaluationSchemeMap R) := by
  change reciprocalChartMap R ⁻¹' Set.range (reciprocalChartMap R ∘ evaluationSchemeMap R) = _
  rw [Set.range_comp]
  exact Set.preimage_image_eq _ (reciprocalChartMap R).isOpenEmbedding.injective

theorem reciprocal_preimage_complement_open :
    reciprocalChartMap R ⁻¹' (sectionComplementOpen R : Set (curveScheme R)) =
      (Set.range (evaluationSchemeMap R))ᶜ := by
  change reciprocalChartMap R ⁻¹'
    (Set.range (ordinaryChartMap R) ∪ Set.range (reciprocalPatchChartMap R)) = _
  rw [Set.preimage_union,Order13MixedActualTwoChartRangeOverlap.reciprocalChartMap_preimage_ordinary_range,
    reciprocalPatchChartMap_range]
  have hi : (reciprocalChartMap R : PrimeSpectrum (reciprocalCoordinateRing R) → curveScheme R) ⁻¹'
      (reciprocalChartMap R '' (PrimeSpectrum.basicOpen (denominator R) : Set (PrimeSpectrum (reciprocalCoordinateRing R)))) =
        (PrimeSpectrum.basicOpen (denominator R) : Set (PrimeSpectrum (reciprocalCoordinateRing R))) :=
    Set.preimage_image_eq _ (reciprocalChartMap R).isOpenEmbedding.injective
  exact (congrArg (fun s : Set (PrimeSpectrum (reciprocalCoordinateRing R)) =>
    (PrimeSpectrum.basicOpen (zCoordinate R) : Set (PrimeSpectrum (reciprocalCoordinateRing R))) ∪ s) hi).trans
      (evaluationSchemeMap_range_complement R).symm

theorem ordinary_chart_disjoint_section_image (a : PrimeSpectrum (ordinaryCoordinateRing R)) :
    ordinaryChartMap R a ∉ Set.range (infinitySectionZero R) := by
  intro h
  change ordinaryChartMap R a ∈ Set.range (reciprocalChartMap R ∘ evaluationSchemeMap R) at h
  rw [Set.range_comp] at h
  obtain ⟨p,hp,heq⟩ := h
  have ho : p ∈ reciprocalChartMap R ⁻¹' Set.range (ordinaryChartMap R) := by
    exact ⟨a,heq.symm⟩
  rw [Order13MixedActualTwoChartRangeOverlap.reciprocalChartMap_preimage_ordinary_range] at ho
  have hz := (mem_evaluationSchemeMap_range R p).mp hp
  exact ho hz.1

theorem ordinary_chart_mem_complement_open (a : PrimeSpectrum (ordinaryCoordinateRing R)) :
    ordinaryChartMap R a ∈ sectionComplementOpen R := by
  change ordinaryChartMap R a ∈ Set.range (ordinaryChartMap R) ∪ Set.range (reciprocalPatchChartMap R)
  exact Or.inl ⟨a,rfl⟩

theorem sectionComplementOpen_eq_section_image_complement :
    (sectionComplementOpen R : Set (curveScheme R)) =
      (Set.range (infinitySectionZero R))ᶜ := by
  ext q
  obtain ⟨i,p,rfl⟩ := (glueData R).openCover.exists_eq q
  cases i with
  | ordinary =>
    exact iff_of_true (ordinary_chart_mem_complement_open R p) (ordinary_chart_disjoint_section_image R p)
  | reciprocal =>
    have hu := Set.ext_iff.mp (reciprocal_preimage_complement_open R) p
    have hs := Set.ext_iff.mp (reciprocal_preimage_section_image R) p
    exact hu.trans (not_congr hs).symm

theorem mem_sectionComplementOpen_iff (q : curveScheme R) :
    q ∈ sectionComplementOpen R ↔
      q ∉ Set.range (infinitySectionZero R) := by
  exact Set.ext_iff.mp (sectionComplementOpen_eq_section_image_complement R) q

end MazurTransfer.Order13MixedActualPositiveInfinityComplement
#print axioms MazurTransfer.Order13MixedActualPositiveInfinityComplement.sectionComplementOpen_eq_section_image_complement

#print axioms MazurTransfer.Order13MixedActualPositiveInfinityComplement.mem_sectionComplementOpen_iff

end


