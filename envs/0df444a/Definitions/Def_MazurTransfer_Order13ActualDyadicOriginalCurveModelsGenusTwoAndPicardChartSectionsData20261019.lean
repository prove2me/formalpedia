-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalCurveModelsGenusTwoAndPicardChartSectionsData20261019
-- name    : MazurTransfer_Order13ActualDyadicOriginalCurveModelsGenusTwoAndPicardChartSectionsData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T07:33:36.607712+00:00
-- url     : https://prove2.me/theorems/0ce249ef-3eea-458f-b0f9-3fd082b754c8
-- title:
--   Actual original dyadic genus-two models and Picard chart sections
-- statement:
--   The original actual mixed curve models, function-field places, structure-sheaf Cech quotient, genus-two Riemann–Roch models and actual Picard chart sections over all specified geometric dyadic fibres. The original six marked sections and all 216 triples retain their chosen constructor values. Named downstream consumer: actual relative degree-zero Picard representability.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original actual dyadic mixed function-field CurveModel,
actual structure-sheaf and place Cech H1, genus-two Riemann-Roch models,
and all 216 ordered marked-section triples satisfying HasChartSections.
Named downstream consumer: actual compatible dyadic Picard representation.
Original per-file headers and exact official Anthropic FLT attribution are retained.
-/
import Mathlib
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq
import Theorems.Thm_AlgebraicCurve_cechH1ToH1_bijective
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_algebraMap_sections_baseChange_of_isReduced
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth
import Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset
import Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq
import Definitions.Def_MazurTransfer_Order13MixedOriginalSingleSectionReciprocalPatchesAndChartEquivalencesDataExplicitEquationDegreeV220261019
import Definitions.Def_MazurTransfer_Order13MixedOriginalSixMarkedSectionsAndPicardChartSelectionData20261019
import Definitions.Def_MazurTransfer_MixedOriginalAffineSectionNaturalityAndLaurentCechCoordinateData20261019
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Theorems.Thm_MazurTransfer_integral_of_two_chart_gluing
import Theorems.Thm_MazurTransfer_order13_actual_mixed_quadratic_both_field_chart_domains
import Theorems.Thm_MazurTransfer_order13_actual_mixed_quadratic_curve_proper
import Theorems.Thm_MazurTransfer_order13_actual_mixed_curve_geometricallyIntegral
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_relative_dimension_and_picard_geometry
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
noncomputable section
universe u
namespace MazurTransfer.Order13MixedQuadraticFieldChartDomains
open MixedQuadraticEquationIrreducible
open Polynomial Module
open MixedQuadraticCoordinateJacobian Order13MixedQuadraticChartFiniteAlgebras Order13MixedQuadraticJacobianCertificates
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates Order13MixedQuadraticOverlapEquivalence
variable (K : Type u) [Field K]
theorem ordinary_x_ne_zero : xCoordinate K ≠ 0 := by
  have hd : (ordinaryEquation K).degree ≠ 0 := by
    rw [degree_eq_natDegree (ordinaryEquation_monic K).ne_zero, equation_natDegree K]
    norm_num
  have hi := AdjoinRoot.of.injective_of_degree_ne_zero hd
  intro hz
  apply X_ne_zero (R := K)
  exact hi (hz.trans (map_zero (AdjoinRoot.of (ordinaryEquation K))).symm)

theorem ordinaryOverlap_isDomain : IsDomain (OrdinaryOverlapRing K) := by
  letI := ordinary_field_isDomain K
  exact Localization.Away.isDomain (ordinary_x_ne_zero K)

end MazurTransfer.Order13MixedQuadraticFieldChartDomains
end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the complete checked two-chart integrality argument of the original
order-thirteen model, using its integral_of_two_chart_gluing theorem.
Design boundary: the ACTUAL mixed quadratic glued curve is integral over
every field, including characteristic two. Named downstream consumer:
geometric integrality of the whole dyadic family for Picard construction.
-/

noncomputable section
namespace MazurTransfer.Order13MixedQuadraticFieldCurveIntegral
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedQuadraticOverlapCoordinates Order13MixedQuadraticFieldChartDomains
universe u
variable (K : Type u) [Field K]

theorem curveScheme_isIntegral : IsIntegral (curveScheme K) := by
  letI : IsDomain (ordinaryCoordinateRing K) := MixedQuadraticEquationIrreducible.ordinary_field_isDomain K
  letI : IsDomain (reciprocalCoordinateRing K) := reciprocal_field_isDomain K
  haveI : IsIntegral ((glueData K).U Chart.ordinary) := by
    change IsIntegral (ordinaryScheme K)
    unfold ordinaryScheme
    exact (affine_isIntegral_iff (.of (ordinaryCoordinateRing K))).mpr inferInstance
  haveI : IsIntegral ((glueData K).U Chart.reciprocal) := by
    change IsIntegral (reciprocalScheme K)
    unfold reciprocalScheme
    exact (affine_isIntegral_iff (.of (reciprocalCoordinateRing K))).mpr inferInstance
  have hv : (glueData K).V (Chart.ordinary, Chart.reciprocal) =
      Spec (.of (OrdinaryOverlapRing K)) := by
    dsimp only [glueData, categoricalGlueData, CategoryTheory.GlueData.ofGlueData']
    exact dif_neg (by intro h; cases h)
  apply MazurTransfer.integral_of_two_chart_gluing (glueData K) Chart.ordinary Chart.reciprocal
  · intro i
    cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [hv]
    letI := ordinaryOverlap_isDomain K
    infer_instance

end MazurTransfer.Order13MixedQuadraticFieldCurveIntegral
#print axioms MazurTransfer.Order13MixedQuadraticFieldCurveIntegral.curveScheme_isIntegral

end
noncomputable section
universe u
namespace MazurTransfer.Order13MixedQuadraticGeometricIntegrality
theorem curveToBase_geometricallyIntegral (R : Type u) [CommRing R] :
    AlgebraicGeometry.GeometricallyIntegral (Order13MixedQuadraticGluedCurve.curveToBase R) :=
  MazurTransfer.order13_actual_mixed_curve_geometricallyIntegral R
end MazurTransfer.Order13MixedQuadraticGeometricIntegrality
end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual smooth proper mixed curve and function-field places
on every field over Z_(2), with its original FLT CurveModel.
Named downstream consumer: characteristic-two genus and Picard chart sections.
Adapts the owned good-characteristic place bridge. Reuses official Anthropic
FLT APIs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/

noncomputable section
namespace MazurTransfer.Order13MixedDyadicFibreCurveModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedQuadraticActualCurveBaseChange
local instance instFactPrimeOfNatNat_order13MixedDyadicFibreCurveModel : Fact (Nat.Prime 2) := ⟨by decide⟩
variable (K : Type) [Field K] [Algebra BaseRing K]

instance actualCurve_isIntegral : IsIntegral (curveScheme K) :=
  Order13MixedQuadraticFieldCurveIntegral.curveScheme_isIntegral K

instance actualCurve_isProper : IsProper (curveToBase K) :=
  MazurTransfer.order13_actual_mixed_quadratic_curve_proper K

instance actualCurve_smoothRelativeDimensionOne : SmoothOfRelativeDimension 1 (curveToBase K) := by
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.of_isPullback (wholeCurve_isPullback BaseRing K)
    MazurTransfer.order13_actual_dyadic_relative_dimension_and_picard_geometry.2.2.1

instance actualCurve_isSmooth : Smooth (curveToBase K) :=
  SmoothOfRelativeDimension.smooth 1 _

instance actualCurve_isNoetherian : IsNoetherian (curveScheme K) := by
  letI : IsLocallyNoetherian (curveScheme K) :=
    LocallyOfFiniteType.isLocallyNoetherian (curveToBase K)
  haveI : CompactSpace (curveScheme K) :=
    QuasiCompact.compactSpace_of_compactSpace (curveToBase K)
  exact ⟨⟩

abbrev actualCurveFunctionField : Type := (curveScheme K).functionField

instance actualCurveFunctionFieldAlgebra : Algebra K (actualCurveFunctionField K) :=
  (baseToFunctionField (curveToBase K)).toAlgebra

def actualPlaceOfPoint (x : closedPoints (curveScheme K)) : Place K (actualCurveFunctionField K) :=
  Classical.choose (_root_.AlgebraicCurve.exists_place_range_stalk_eq
    (curveToBase K) x.1 (mem_closedPoints_iff.mp x.2))

theorem actualPlaceOfPoint_stalk_range (x : closedPoints (curveScheme K)) :
    (algebraMap ((curveScheme K).presheaf.stalk x.1) (actualCurveFunctionField K)).range =
      (actualPlaceOfPoint K x).toValuationSubring.toSubring :=
  Classical.choose_spec (_root_.AlgebraicCurve.exists_place_range_stalk_eq
    (curveToBase K) x.1 (mem_closedPoints_iff.mp x.2))

theorem actualPlaceOfPoint_bijective : Function.Bijective (actualPlaceOfPoint K) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact _root_.AlgebraicCurve.eq_of_range_stalk_eq (curveToBase K) x.1 y.1
      (by rw [actualPlaceOfPoint_stalk_range, actualPlaceOfPoint_stalk_range, hxy])
  · intro v
    obtain ⟨x, hx, hrange⟩ :=
      _root_.AlgebraicCurve.exists_closedPoint_range_stalk_eq (curveToBase K) v
    refine ⟨⟨x, mem_closedPoints_iff.mpr hx⟩, Place.ext ?_⟩
    apply ValuationSubring.toSubring_injective
    rw [← actualPlaceOfPoint_stalk_range, hrange]


instance actualFunctionFieldIsCurveOver [PerfectField K] : IsCurveOver K (actualCurveFunctionField K) :=
  AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    (curveToBase K) (RingEquiv.refl _) (fun _ => rfl)

def actualCurveModel [IsAlgClosed K] : CurveModel K (actualCurveFunctionField K) where
  C := curveScheme K
  toBase := curveToBase K
  ffEquiv := RingEquiv.refl _
  ffEquiv_algebraMap := fun _ => rfl
  placeOfPoint := actualPlaceOfPoint K
  placeOfPoint_bijective := actualPlaceOfPoint_bijective K
  range_stalk_eq := fun x => by
    rw [← actualPlaceOfPoint_stalk_range K x]
    ext f
    simp
  finset_subset_affineOpen := fun F =>
    exists_isAffineOpen_forall_mem_of_finset (curveToBase K) F


end MazurTransfer.Order13MixedDyadicFibreCurveModel
#print axioms MazurTransfer.Order13MixedDyadicFibreCurveModel.actualCurveModel

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual ordinary/reciprocal affine cover and exact overlap
of the mixed order-13 curve over every commutative ring.
Named downstream consumer: mixed structure-sheaf Cech cohomology.
Adapts the owned square-model cover proof to the literal mixed gluing.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedActualChartCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticTransitionHomomorphisms Order13MixedQuadraticGluedCurve
variable (K : Type u) [CommRing K]

instance ordinaryScheme_isAffine : IsAffine (ordinaryScheme K) := by
  unfold ordinaryScheme
  infer_instance

instance reciprocalScheme_isAffine : IsAffine (reciprocalScheme K) := by
  unfold reciprocalScheme
  infer_instance

def ordinaryOpen : (curveScheme K).Opens := (ordinaryChartMap K).opensRange
def reciprocalOpen : (curveScheme K).Opens := (reciprocalChartMap K).opensRange

theorem chart_opens_sup_eq_top : ordinaryOpen K ⊔ reciprocalOpen K = ⊤ := by
  apply top_unique
  intro x _
  change x ∈ Set.range (ordinaryChartMap K) ∨ x ∈ Set.range (reciprocalChartMap K)
  obtain ⟨i, y, hy⟩ := (glueData K).ι_jointly_surjective x
  cases i
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

theorem curveScheme_isSeparated : (curveScheme K).IsSeparated := by
  haveI : IsProper (curveToBase K) := MazurTransfer.order13_actual_mixed_quadratic_curve_proper K
  have h : IsSeparated (curveToBase K ≫ terminal.from (Spec (.of K))) := inferInstance
  refine ⟨?_⟩
  simpa only [terminal.comp_from] using h

def actualTwoAffineOpenCover : (curveScheme K).TwoAffineOpenCover := by
  haveI := curveScheme_isSeparated K
  exact {
    U0 := ordinaryOpen K
    U1 := reciprocalOpen K
    isAffineOpen_U0 := isAffineOpen_opensRange (ordinaryChartMap K)
    isAffineOpen_U1 := isAffineOpen_opensRange (reciprocalChartMap K)
    sup_eq_top := chart_opens_sup_eq_top K
    isAffineOpen_inf := (isAffineOpen_opensRange (ordinaryChartMap K)).inf
      (isAffineOpen_opensRange (reciprocalChartMap K)) }

def ordinaryOverlapMap : Spec (.of (OrdinaryOverlapRing K)) ⟶ ordinaryScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing K)
    (OrdinaryOverlapRing K)))

def reciprocalOverlapMap : Spec (.of (OrdinaryOverlapRing K)) ⟶ reciprocalScheme K :=
  Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase K).toRingHom)

def overlapToCurve : Spec (.of (OrdinaryOverlapRing K)) ⟶ curveScheme K :=
  ordinaryOverlapMap K ≫ ordinaryChartMap K

instance ordinaryOverlapMap_isOpenImmersion : IsOpenImmersion (ordinaryOverlapMap K) :=
  IsOpenImmersion.of_isLocalization (xCoordinate K)

instance overlapToCurve_isOpenImmersion : IsOpenImmersion (overlapToCurve K) := by
  exact IsOpenImmersion.comp (ordinaryOverlapMap K) (ordinaryChartMap K)

theorem overlapToCurve_eq_reciprocal :
    overlapToCurve K = reciprocalOverlapMap K ≫ reciprocalChartMap K := by
  have hmap : Spec.map (CommRingCat.ofHom (reciprocalToOrdinary K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (reciprocalCoordinateRing K) (ReciprocalOverlapRing K))) =
        reciprocalOverlapMap K := by
    rw [← Spec.map_comp]
    apply Spec.map_inj.mpr
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact reciprocalToOrdinary_algebraMap K a
  have H := Order13MixedQuadraticActualCurveBaseChange.ordinary_reciprocal_glue K
  apply H.trans
  apply (Category.assoc _ _ (reciprocalChartMap K)).symm.trans
  exact congrArg (fun f : Spec (.of (OrdinaryOverlapRing K)) ⟶ reciprocalScheme K =>
    f ≫ reciprocalChartMap K) hmap

theorem overlap_opensRange :
    (overlapToCurve K).opensRange = ordinaryOpen K ⊓ reciprocalOpen K := by
  have hr : Set.range (ordinaryOverlapMap K) =
      (PrimeSpectrum.basicOpen (xCoordinate K) : Set (PrimeSpectrum (ordinaryCoordinateRing K))) :=
    PrimeSpectrum.localization_away_comap_range (OrdinaryOverlapRing K) (xCoordinate K)
  have hp := congrArg (fun U : (ordinaryScheme K).Opens => (U : Set (ordinaryScheme K)))
    (Order13MixedQuadraticHyperellipticMap.ordinaryChartMap_preimage_reciprocalChartMap_opensRange_eq_basicOpen K)
  change ordinaryChartMap K ⁻¹' Set.range (reciprocalChartMap K) = _ at hp
  apply TopologicalSpace.Opens.ext
  change Set.range ((ordinaryChartMap K) ∘ (ordinaryOverlapMap K)) =
    Set.range (ordinaryChartMap K) ∩ Set.range (reciprocalChartMap K)
  apply (Set.range_comp (ordinaryChartMap K) (ordinaryOverlapMap K)).trans
  apply (congrArg (fun S : Set (ordinaryScheme K) => ordinaryChartMap K '' S)
    (hr.trans hp.symm)).trans
  exact Set.image_preimage_eq_inter_range.trans (Set.inter_comm _ _)

end MazurTransfer.Order13MixedActualChartCover
#print axioms MazurTransfer.Order13MixedActualChartCover.actualTwoAffineOpenCover
#print axioms MazurTransfer.Order13MixedActualChartCover.overlap_opensRange

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual mixed order-13 affine rings and transition
have a two-dimensional Laurent coefficient quotient over every field.
Named downstream consumer: actual structure-sheaf Cech H1 and genus two.
Adapts the owned Order13ActualCechQuotient proof and its Laurent quotient.
-/

noncomputable section
namespace MazurTransfer.Order13MixedActualCechQuotient
open Polynomial Module
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticJacobianCertificates
open Order13MixedQuadraticOverlapCoordinates Order13MixedQuadraticTransitionHomomorphisms
open MazurTransfer
variable (K : Type*) [Field K]
abbrev QuadraticLaurentRing := _root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.LaurentChart K (ordinaryH K) (ordinaryF K)

def overlapAlgEquiv : OrdinaryOverlapRing K ≃ₐ[K] QuadraticLaurentRing K :=
  _root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.overlapAlgEquiv K (ordinaryH K) (ordinaryF K)

def overlapCoordinates : OrdinaryOverlapRing K ≃ₗ[K] MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019.OverlapCoefficients K :=
  (overlapAlgEquiv K).toLinearEquiv.trans
    (((_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates (LaurentPolynomial K) (ordinaryH K).toLaurent (ordinaryF K).toLaurent).restrictScalars K).trans
      ((AddMonoidAlgebra.coeffLinearEquiv K).prodCongr (AddMonoidAlgebra.coeffLinearEquiv K)))

def ordinaryCoordinates : ordinaryCoordinateRing K ≃ₗ[K] MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019.ChartCoefficients K × MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019.ChartCoefficients K :=
  ((_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates (Polynomial K) (ordinaryH K) (ordinaryF K)).restrictScalars K).trans
    (((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)).prodCongr
      ((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)))

def reciprocalCoordinates : reciprocalCoordinateRing K ≃ₗ[K] MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019.ChartCoefficients K × MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019.ChartCoefficients K :=
  ((_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates (Polynomial K) (reciprocalH K) (reciprocalF K)).restrictScalars K).trans
    (((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)).prodCongr
      ((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)))

theorem overlapCoordinates_of_add_of_mul_root (a b : LaurentPolynomial K) :
    overlapCoordinates K ((overlapAlgEquiv K).symm
      (AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) a +
        AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) b *
          AdjoinRoot.root (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)))) = (a.coeff, b.coeff) := by
  change ((AddMonoidAlgebra.coeffLinearEquiv K).prodCongr (AddMonoidAlgebra.coeffLinearEquiv K))
    (_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates (LaurentPolynomial K) (ordinaryH K).toLaurent (ordinaryF K).toLaurent
      ((overlapAlgEquiv K) ((overlapAlgEquiv K).symm _))) = _
  rw [AlgEquiv.apply_symm_apply]
  change ((AddMonoidAlgebra.coeffLinearEquiv K).prodCongr (AddMonoidAlgebra.coeffLinearEquiv K))
    (_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates (LaurentPolynomial K) (ordinaryH K).toLaurent (ordinaryF K).toLaurent
      (AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.equation _ _ _) a + AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.equation _ _ _) b *
        AdjoinRoot.root (_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.equation _ _ _))) = _
  rw [_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates_of_add_of_mul_root]
  rfl

theorem laurent_inverse_coordinate :
    overlapAlgEquiv K (IsLocalization.Away.invSelf (xCoordinate K)) =
      AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) (LaurentPolynomial.T (-1)) := by
  let o := AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K))
  have hu : IsUnit (o (LaurentPolynomial.T 1)) :=
    (LaurentPolynomial.isUnit_T (1 : ℤ)).map o
  apply hu.mul_left_cancel
  have hx : overlapAlgEquiv K (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K) (xCoordinate K)) =
      o (LaurentPolynomial.T 1) := by
    change _root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.toLaurent K (ordinaryH K) (ordinaryF K)
      (algebraMap _ _ (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.x K (ordinaryH K) (ordinaryF K))) = _
    rw [_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.toLaurent_algebraMap]
    exact _root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.toLaurentBase_x K (ordinaryH K) (ordinaryF K)
  rw [← hx, ← map_mul, IsLocalization.Away.mul_invSelf, map_one, hx]
  change 1 = o (LaurentPolynomial.T 1) * o (LaurentPolynomial.T (-1))
  rw [← map_mul, ← LaurentPolynomial.T_add]
  simp only [Int.reduceAdd, LaurentPolynomial.T_zero, map_one]

theorem reciprocal_z_laurent :
    overlapAlgEquiv K (reciprocalToOrdinaryBase K (zCoordinate K)) =
      AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) (LaurentPolynomial.T (-1)) := by
  rw [reciprocalToOrdinaryBase_z]
  exact laurent_inverse_coordinate K

theorem reciprocal_w_laurent :
    overlapAlgEquiv K (reciprocalToOrdinaryBase K (wCoordinate K)) =
      AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) (LaurentPolynomial.T (-3)) *
        AdjoinRoot.root (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) := by
  rw [reciprocalToOrdinaryBase_w]
  change overlapAlgEquiv K
    (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K) *
      (IsLocalization.Away.invSelf (xCoordinate K)) ^ 3) = _
  rw [map_mul, map_pow, laurent_inverse_coordinate]
  have hy : overlapAlgEquiv K (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K)) =
      AdjoinRoot.root (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) := by
    change _root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.toLaurent K (ordinaryH K) (ordinaryF K)
      (algebraMap _ _ (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.y K (ordinaryH K) (ordinaryF K))) = _
    rw [_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.toLaurent_algebraMap]
    exact _root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.toLaurentBase_y K (ordinaryH K) (ordinaryF K)
  rw [hy, ← map_pow, LaurentPolynomial.T_pow]
  norm_num only
  rw [mul_comm]

theorem invert_toLaurent_coeff (p : Polynomial K) :
    (LaurentPolynomial.invert p.toLaurent).coeff =
      Finsupp.mapDomain (fun n : ℕ => -(n : ℤ)) p.toFinsupp.coeff := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, AddMonoidAlgebra.coeff_add, Polynomial.toFinsupp_add,
        Finsupp.mapDomain_add] using congrArg₂ (· + ·) hp hq
  | monomial n a =>
      rw [Polynomial.toLaurent_C_mul_T]
      rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
        ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_single, Polynomial.toFinsupp_monomial, Finsupp.mapDomain_single]

theorem invert_toLaurent_shift_coeff (p : Polynomial K) :
    (LaurentPolynomial.invert p.toLaurent * LaurentPolynomial.T (-3)).coeff =
      Finsupp.mapDomain (fun n : ℕ => -(n : ℤ) - 3) p.toFinsupp.coeff := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Polynomial.toFinsupp_add,
        Finsupp.mapDomain_add] using congrArg₂ (· + ·) hp hq
  | monomial n a =>
      rw [Polynomial.toLaurent_C_mul_T]
      rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
        LaurentPolynomial.mul_T_assoc, ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_single, Polynomial.toFinsupp_monomial, Finsupp.mapDomain_single]
      rfl

def actualBoundaries : Submodule K (OrdinaryOverlapRing K) :=
  (Algebra.algHom K (ordinaryCoordinateRing K) (OrdinaryOverlapRing K)).toLinearMap.range ⊔
    (reciprocalToOrdinaryBase K).toLinearMap.range

theorem ordinary_laurent (p : Polynomial K) :
    overlapAlgEquiv K (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K)
      (AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation K (ordinaryH K) (ordinaryF K)) p)) =
        AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) p.toLaurent := by
  change _root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.toLaurent K (ordinaryH K) (ordinaryF K)
    (algebraMap _ _ (AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.equation K (ordinaryH K) (ordinaryF K)) p)) = _
  rw [_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.toLaurent_algebraMap]
  simp [_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.toLaurentBase]

theorem ordinary_y_laurent :
    overlapAlgEquiv K (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K)) =
      AdjoinRoot.root (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) := by
  change _root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.toLaurent K (ordinaryH K) (ordinaryF K)
    (algebraMap _ _ (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.y K (ordinaryH K) (ordinaryF K))) = _
  rw [_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.toLaurent_algebraMap]
  exact _root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.toLaurentBase_y K (ordinaryH K) (ordinaryF K)

theorem reciprocal_laurent (p : Polynomial K) :
    overlapAlgEquiv K (reciprocalToOrdinaryBase K (AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation K (reciprocalH K) (reciprocalF K)) p)) =
      AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K))
        (LaurentPolynomial.invert p.toLaurent) := by
  have h : ((overlapAlgEquiv K).toAlgHom.comp (reciprocalToOrdinaryBase K)).comp
      (AdjoinRoot.ofAlgHom K (MixedQuadraticCoordinateJacobian.equation K (reciprocalH K) (reciprocalF K))) =
    (AdjoinRoot.ofAlgHom K (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K))).comp
      (LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg) := by
    apply Polynomial.algHom_ext
    change overlapAlgEquiv K (reciprocalToOrdinaryBase K (zCoordinate K)) =
      AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K))
        (LaurentPolynomial.invert (Polynomial.toLaurent (X : Polynomial K)))
    rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T]
    exact reciprocal_z_laurent K
  exact DFunLike.congr_fun h p

theorem ordinary_diagram (a : ordinaryCoordinateRing K) :
    overlapCoordinates K (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K) a) =
      MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019.ordinary K (ordinaryCoordinates K a) := by
  let p := _root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates (Polynomial K) (ordinaryH K) (ordinaryF K) a
  have ha : a = AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation K (ordinaryH K) (ordinaryF K)) p.1 +
      AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation K (ordinaryH K) (ordinaryF K)) p.2 * yCoordinate K := by
    exact (_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates_symm (Polynomial K) (ordinaryH K) (ordinaryF K) p).symm.trans
      ((_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates (Polynomial K) (ordinaryH K) (ordinaryF K)).symm_apply_apply a) |>.symm
  have he : overlapAlgEquiv K (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K) a) =
      AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) p.1.toLaurent +
        AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) p.2.toLaurent *
          AdjoinRoot.root (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) := by
    rw [ha, map_add, map_mul, map_add, map_mul, ordinary_laurent, ordinary_laurent,
      ordinary_y_laurent]
  have he' := congrArg (overlapAlgEquiv K).symm he
  rw [AlgEquiv.symm_apply_apply] at he'
  rw [he', overlapCoordinates_of_add_of_mul_root]
  rfl

theorem reciprocal_diagram (a : reciprocalCoordinateRing K) :
    overlapCoordinates K (reciprocalToOrdinaryBase K a) =
      MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019.reciprocal K (reciprocalCoordinates K a) := by
  let p := _root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates (Polynomial K) (reciprocalH K) (reciprocalF K) a
  have ha : a = AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation K (reciprocalH K) (reciprocalF K)) p.1 +
      AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation K (reciprocalH K) (reciprocalF K)) p.2 * wCoordinate K := by
    exact (_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates_symm (Polynomial K) (reciprocalH K) (reciprocalF K) p).symm.trans
      ((_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates (Polynomial K) (reciprocalH K) (reciprocalF K)).symm_apply_apply a) |>.symm
  have he : overlapAlgEquiv K (reciprocalToOrdinaryBase K a) =
      AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K))
        (LaurentPolynomial.invert p.1.toLaurent) +
        AdjoinRoot.of (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K))
          (LaurentPolynomial.invert p.2.toLaurent * LaurentPolynomial.T (-3)) *
          AdjoinRoot.root (_root_.MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.laurentEquation K (ordinaryH K) (ordinaryF K)) := by
    rw [ha, map_add, map_mul, map_add, map_mul, reciprocal_laurent, reciprocal_laurent,
      reciprocal_w_laurent, map_mul]
    ring
  have he' := congrArg (overlapAlgEquiv K).symm he
  rw [AlgEquiv.symm_apply_apply] at he'
  rw [he', overlapCoordinates_of_add_of_mul_root, invert_toLaurent_coeff,
    invert_toLaurent_shift_coeff]
  rfl

theorem actualBoundaries_image :
    (actualBoundaries K).map (overlapCoordinates K).toLinearMap =
      MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019.boundaries K := by
  rw [actualBoundaries, MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019.boundaries, Submodule.map_sup]
  congr 1
  · ext v
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨ordinaryCoordinates K a, (ordinary_diagram K a).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K)
        ((ordinaryCoordinates K).symm c), ⟨(ordinaryCoordinates K).symm c, rfl⟩, ?_⟩
      change overlapCoordinates K
        (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K) ((ordinaryCoordinates K).symm c)) = _
      rw [ordinary_diagram, LinearEquiv.apply_symm_apply]
  · ext v
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨reciprocalCoordinates K a, (reciprocal_diagram K a).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨reciprocalToOrdinaryBase K ((reciprocalCoordinates K).symm c),
        ⟨(reciprocalCoordinates K).symm c, rfl⟩, ?_⟩
      change overlapCoordinates K
        (reciprocalToOrdinaryBase K ((reciprocalCoordinates K).symm c)) = _
      rw [reciprocal_diagram, LinearEquiv.apply_symm_apply]

def quotientEquiv : (OrdinaryOverlapRing K ⧸ actualBoundaries K) ≃ₗ[K] K × K :=
  (Submodule.Quotient.equiv (actualBoundaries K) (MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019.boundaries K)
    (overlapCoordinates K) (actualBoundaries_image K)).trans
      (MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019.quotientEquiv K)

theorem actual_two_chart_section_quotient_finrank :
    Module.finrank K (OrdinaryOverlapRing K ⧸ actualBoundaries K) = 2 := by
  rw [(quotientEquiv K).finrank_eq]
  simp

def reciprocalPolynomialSections : (Polynomial K × Polynomial K) →ₗ[K] OrdinaryOverlapRing K :=
  let coeff := (Polynomial.aeval (IsLocalization.Away.invSelf (xCoordinate K)) :
    Polynomial K →ₐ[K] OrdinaryOverlapRing K).toLinearMap
  coeff.coprod ((LinearMap.mulRight K
    (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K) *
      (IsLocalization.Away.invSelf (xCoordinate K)) ^ 3)).comp coeff)

theorem reciprocal_sections_formula (p : Polynomial K × Polynomial K) :
    reciprocalToOrdinaryBase K
      (AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation K (reciprocalH K) (reciprocalF K)) p.1 +
        AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation K (reciprocalH K) (reciprocalF K)) p.2 * wCoordinate K) =
      reciprocalPolynomialSections K p := by
  rw [map_add, map_mul]
  simp only [reciprocalToOrdinaryBase, AdjoinRoot.liftAlgHom_of,
    wCoordinate, AdjoinRoot.liftAlgHom_root]
  rfl

theorem reciprocal_polynomial_sections_range :
    (reciprocalToOrdinaryBase K).toLinearMap.range =
      (reciprocalPolynomialSections K).range := by
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    let p := _root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates (Polynomial K) (reciprocalH K) (reciprocalF K) a
    refine ⟨p, ?_⟩
    rw [← reciprocal_sections_formula]
    apply congrArg (reciprocalToOrdinaryBase K)
    exact (_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates_symm (Polynomial K) (reciprocalH K) (reciprocalF K) p).symm.trans
      ((_root_.MazurTransfer.MixedOriginalFiniteMapCoordinateRewrite20261019.coordinates (Polynomial K) (reciprocalH K) (reciprocalF K)).symm_apply_apply a)
  · rintro ⟨p, rfl⟩
    exact ⟨AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation K (reciprocalH K) (reciprocalF K)) p.1 +
      AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation K (reciprocalH K) (reciprocalF K)) p.2 * wCoordinate K,
      reciprocal_sections_formula K p⟩

theorem actual_quotient_finrank_polynomial_sections :
    Module.finrank K (OrdinaryOverlapRing K ⧸
      ((Algebra.algHom K (ordinaryCoordinateRing K) (OrdinaryOverlapRing K)).toLinearMap.range ⊔
        (reciprocalPolynomialSections K).range)) = 2 := by
  rw [← reciprocal_polynomial_sections_range]
  exact actual_two_chart_section_quotient_finrank K

end MazurTransfer.Order13MixedActualCechQuotient
#print axioms MazurTransfer.Order13MixedActualCechQuotient.actual_two_chart_section_quotient_finrank

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual affine-coordinate section equivalences commute
with ordinary and reciprocal restriction to the mixed curve overlap.
Named downstream consumer: actual mixed-curve structure-sheaf Cech H1.
Adapts the owned square-model section and Cech comparison; no genus is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedActualStructureSheafCech
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticTransitionHomomorphisms Order13MixedQuadraticGluedCurve
open Order13MixedActualChartCover Order13MixedActualCechQuotient
variable (K : Type u) [Field K]

abbrev sectionsCover := (actualTwoAffineOpenCover K).cover (curveToBase K)
abbrev actualStructureSheafSections := (actualTwoAffineOpenCover K).structureSheafSections (curveToBase K)

theorem overlapToCurve_curveToBase :
    overlapToCurve K ≫ curveToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K (OrdinaryOverlapRing K))) := by
  have he := congrArg (fun f : ordinaryScheme K ⟶ Spec (.of K) => ordinaryOverlapMap K ≫ f)
    (ordinaryChartMap_curveToBase K)
  apply (Category.assoc (ordinaryOverlapMap K) (ordinaryChartMap K) (curveToBase K)).trans
  apply he.trans
  change Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (ordinaryCoordinateRing K))) = _
  rw [← Spec.map_comp]
  apply Spec.map_inj.mpr
  apply CommRingCat.hom_ext
  exact IsScalarTower.algebraMap_eq K (ordinaryCoordinateRing K) (OrdinaryOverlapRing K)

def ordinaryChartFromSpec : Spec (.of (ordinaryCoordinateRing K)) ⟶ curveScheme K :=
  ordinaryChartMap K

def reciprocalChartFromSpec : Spec (.of (reciprocalCoordinateRing K)) ⟶ curveScheme K :=
  reciprocalChartMap K

instance ordinaryChartFromSpec_isOpenImmersion : IsOpenImmersion (ordinaryChartFromSpec K) :=
  Order13MixedQuadraticGluedCurve.ordinaryChartMap_isOpenImmersion K

instance reciprocalChartFromSpec_isOpenImmersion : IsOpenImmersion (reciprocalChartFromSpec K) :=
  Order13MixedQuadraticGluedCurve.reciprocalChartMap_isOpenImmersion K

def ordinarySectionsEquiv :
    (sectionsCover K).A0 ≃ₐ[K] ordinaryCoordinateRing K :=
  MixedOriginalDyadicAffineOpenCoordinateSectionsAt20261019.sectionsAlgEquivAt (X := curveScheme K)
    (ordinaryCoordinateRing K) (ordinaryChartFromSpec K) K (curveToBase K)
    (ordinaryOpen K) rfl (ordinaryChartMap_curveToBase K)

def reciprocalSectionsEquiv :
    (sectionsCover K).A1 ≃ₐ[K] reciprocalCoordinateRing K :=
  MixedOriginalDyadicAffineOpenCoordinateSectionsAt20261019.sectionsAlgEquivAt (X := curveScheme K)
    (reciprocalCoordinateRing K) (reciprocalChartFromSpec K) K (curveToBase K) (reciprocalOpen K) rfl (reciprocalChartMap_curveToBase K)

def overlapSectionsEquiv :
    (sectionsCover K).A01 ≃ₐ[K] OrdinaryOverlapRing K :=
  MixedOriginalDyadicAffineOpenCoordinateSectionsAt20261019.sectionsAlgEquivAt (X := curveScheme K)
    (OrdinaryOverlapRing K) (overlapToCurve K) K (curveToBase K) (ordinaryOpen K ⊓ reciprocalOpen K)
    (overlap_opensRange K) (overlapToCurve_curveToBase K)

theorem ordinarySectionsEquiv_apply (z : (sectionsCover K).A0) :
    ordinarySectionsEquiv K z =
      (MixedOriginalDyadicAffineOpenCoordinateSectionsAt20261019.sectionsRingIsoAt (X := curveScheme K) (ordinaryCoordinateRing K)
        (ordinaryChartFromSpec K) (ordinaryOpen K) rfl).hom.hom z := rfl

theorem reciprocalSectionsEquiv_apply (z : (sectionsCover K).A1) :
    reciprocalSectionsEquiv K z =
      (MixedOriginalDyadicAffineOpenCoordinateSectionsAt20261019.sectionsRingIsoAt (X := curveScheme K) (reciprocalCoordinateRing K)
        (reciprocalChartFromSpec K) (reciprocalOpen K) rfl).hom.hom z := rfl

theorem overlapSectionsEquiv_apply (z : (sectionsCover K).A01) :
    overlapSectionsEquiv K z =
      (MixedOriginalDyadicAffineOpenCoordinateSectionsAt20261019.sectionsRingIsoAt (X := curveScheme K) (OrdinaryOverlapRing K)
        (overlapToCurve K) (ordinaryOpen K ⊓ reciprocalOpen K)
        (overlap_opensRange K)).hom.hom z :=
  MixedOriginalDyadicAffineOpenCoordinateSectionsAt20261019.sectionsAlgEquivAt_apply (X := curveScheme K)
    (OrdinaryOverlapRing K) (overlapToCurve K) K (curveToBase K)
    (ordinaryOpen K ⊓ reciprocalOpen K) (overlap_opensRange K)
    (overlapToCurve_curveToBase K) z

theorem ordinarySections_restrict (z : (sectionsCover K).A0) :
    overlapSectionsEquiv K ((sectionsCover K).ρ0 z) =
      algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K)
        (ordinarySectionsEquiv K z) := by
  rw [overlapSectionsEquiv_apply, ordinarySectionsEquiv_apply,
    Scheme.TwoAffineOpenCover.cover_ρ0_apply]
  exact congrArg (fun t : Γ(curveScheme K, ordinaryOpen K) ⟶
      CommRingCat.of (OrdinaryOverlapRing K) => t.hom z)
    (MixedOriginalDyadicAffineOpenCoordinateSectionsAt20261019.sectionsRingIsoAt_restriction (X := curveScheme K)
      (ordinaryCoordinateRing K) (ordinaryChartFromSpec K)
      (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K))
      (overlapToCurve K) rfl (ordinaryOpen K) (ordinaryOpen K ⊓ reciprocalOpen K)
      rfl (overlap_opensRange K) inf_le_left)

theorem reciprocalSections_restrict (z : (sectionsCover K).A1) :
    overlapSectionsEquiv K ((sectionsCover K).ρ1 z) =
      reciprocalToOrdinaryBase K (reciprocalSectionsEquiv K z) := by
  rw [overlapSectionsEquiv_apply, reciprocalSectionsEquiv_apply,
    Scheme.TwoAffineOpenCover.cover_ρ1_apply]
  exact congrArg (fun t : Γ(curveScheme K, reciprocalOpen K) ⟶
      CommRingCat.of (OrdinaryOverlapRing K) => t.hom z)
    (MixedOriginalDyadicAffineOpenCoordinateSectionsAt20261019.sectionsRingIsoAt_restriction (X := curveScheme K)
      (reciprocalCoordinateRing K) (reciprocalChartFromSpec K)
      (reciprocalToOrdinaryBase K).toRingHom
      (overlapToCurve K) (overlapToCurve_eq_reciprocal K).symm
      (reciprocalOpen K) (ordinaryOpen K ⊓ reciprocalOpen K)
      rfl (overlap_opensRange K) inf_le_right)


end MazurTransfer.Order13MixedActualStructureSheafCech
#print axioms MazurTransfer.Order13MixedActualStructureSheafCech.ordinarySections_restrict
#print axioms MazurTransfer.Order13MixedActualStructureSheafCech.reciprocalSections_restrict

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original structure-sheaf sections of the actual mixed curve
have Cech H1 of dimension two over every field, via exact chart restrictions.
Named downstream consumer: characteristic-two function-field genus bridge.
Adapts the owned square-model section and Cech comparison; no genus is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedActualStructureSheafCech
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticTransitionHomomorphisms Order13MixedQuadraticGluedCurve
open Order13MixedActualChartCover Order13MixedActualCechQuotient
variable (K : Type u) [Field K]

def coordinateCechDiff :
    (ordinaryCoordinateRing K × reciprocalCoordinateRing K) →ₗ[K] OrdinaryOverlapRing K :=
  (-(Algebra.algHom K (ordinaryCoordinateRing K) (OrdinaryOverlapRing K)).toLinearMap).coprod
    (reciprocalToOrdinaryBase K).toLinearMap

theorem coordinateCechDiff_range : (coordinateCechDiff K).range = actualBoundaries K := by
  rw [coordinateCechDiff, LinearMap.range_coprod, LinearMap.range_neg]
  rfl

def actualStructureSheafH1Equiv :
    (actualStructureSheafSections K).H1 ≃ₗ[K] (OrdinaryOverlapRing K ⧸ actualBoundaries K) :=
  MixedOriginalDyadicTwoChartCechCoordinateComparison20261019.quotientEquiv (sectionsCover K)
    (ordinarySectionsEquiv K).toLinearEquiv (reciprocalSectionsEquiv K).toLinearEquiv
    (overlapSectionsEquiv K).toLinearEquiv
    (Algebra.algHom K (ordinaryCoordinateRing K) (OrdinaryOverlapRing K)).toLinearMap
    (reciprocalToOrdinaryBase K).toLinearMap
    (ordinarySections_restrict K) (reciprocalSections_restrict K)
    (actualBoundaries K) (coordinateCechDiff_range K)

theorem actual_structureSheaf_cechH1_finrank :
    Module.finrank K (actualStructureSheafSections K).H1 = 2 := by
  rw [(actualStructureSheafH1Equiv K).finrank_eq]
  exact actual_two_chart_section_quotient_finrank K


end MazurTransfer.Order13MixedActualStructureSheafCech
#print axioms MazurTransfer.Order13MixedActualStructureSheafCech.actual_structureSheaf_cechH1_finrank

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual mixed curve over a perfect field above Z_(2)
has function-field genus two, via its genuine section and place Cech H1.
Named downstream consumer: genus-two Riemann-Roch for Picard chart sections.
Adapts the owned good-characteristic genus bridge using the newly checked
mixed charts; official Anthropic FLT APIs retain their exact source pin.
-/

noncomputable section
namespace MazurTransfer.Order13MixedDyadicFibreGenus
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedDyadicFibreCurveModel Order13MixedActualChartCover
open Order13MixedActualStructureSheafCech
local instance instFactPrimeOfNatNat_order13MixedDyadicFibreGenus : Fact (Nat.Prime 2) := ⟨by decide⟩
variable (K : Type) [Field K] [Algebra BaseRing K] [PerfectField K]

theorem actual_curve_not_isAffine : ¬ IsAffine (curveScheme K) :=
  AlgebraicGeometry.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
    (curveToBase K)

theorem actual_affineOpen_ne_top (U : (curveScheme K).Opens) (hU : IsAffineOpen U) :
    U ≠ ⊤ := by
  intro h
  have hT : IsAffineOpen (⊤ : (curveScheme K).Opens) := h ▸ hU
  haveI : IsAffine (⊤ : (curveScheme K).Opens) := hT
  exact actual_curve_not_isAffine K (IsAffine.of_isIso (curveScheme K).topIso.inv)

theorem actual_places_cover_nonempty_complements :
    placesOf (curveToBase K) (actualTwoAffineOpenCover K).U0 ∪
        placesOf (curveToBase K) (actualTwoAffineOpenCover K).U1 = Set.univ ∧
      (∃ v : Place K (actualCurveFunctionField K),
        v ∉ placesOf (curveToBase K) (actualTwoAffineOpenCover K).U0) ∧
      (∃ v : Place K (actualCurveFunctionField K),
        v ∉ placesOf (curveToBase K) (actualTwoAffineOpenCover K).U1) := by
  exact _root_.AlgebraicCurve.placesOf_union_eq_univ_of_sup_eq_top
    (curveToBase K) (actualTwoAffineOpenCover K).U0 (actualTwoAffineOpenCover K).U1
    (actualTwoAffineOpenCover K).sup_eq_top
    (actual_affineOpen_ne_top K _ (actualTwoAffineOpenCover K).isAffineOpen_U0)
    (actual_affineOpen_ne_top K _ (actualTwoAffineOpenCover K).isAffineOpen_U1)

theorem actual_placesOf_inf (U V : (curveScheme K).Opens) :
    placesOf (curveToBase K) (U ⊓ V) =
      placesOf (curveToBase K) U ∩ placesOf (curveToBase K) V := by
  ext v
  constructor
  · rintro ⟨x, hx, hclosed, hrange⟩
    exact ⟨⟨x, hx.1, hclosed, hrange⟩, ⟨x, hx.2, hclosed, hrange⟩⟩
  · rintro ⟨⟨x, hxU, hxclosed, hxrange⟩, ⟨y, hyV, _, hyrange⟩⟩
    have hxy : x = y := _root_.AlgebraicCurve.eq_of_range_stalk_eq
      (curveToBase K) x y (hxrange.trans hyrange.symm)
    subst y
    exact ⟨x, ⟨hxU, hyV⟩, hxclosed, hxrange⟩

theorem actual_cover_open_nonempty (U V : (curveScheme K).Opens)
    (hUV : U ⊔ V = ⊤) (hV : IsAffineOpen V) : Nonempty U := by
  have hUne : (U : Set (curveScheme K)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hU0 : U = ⊥ := TopologicalSpace.Opens.ext h
    rw [hU0, bot_sup_eq] at hUV
    exact actual_affineOpen_ne_top K V hV hUV
  exact hUne.to_subtype

abbrev actualPlaceCechH1 : Type :=
  cechH1 (placesOf (curveToBase K) (actualTwoAffineOpenCover K).U0)
    (placesOf (curveToBase K) (actualTwoAffineOpenCover K).U1)
    (0 : Divisor K (actualCurveFunctionField K))

theorem actual_structureSheaf_placeCechH1_equiv :
    Nonempty ((actualStructureSheafSections K).H1 ≃ₗ[K] actualPlaceCechH1 K) := by
  have h0 := actual_cover_open_nonempty K _ _
    (actualTwoAffineOpenCover K).sup_eq_top
    (actualTwoAffineOpenCover K).isAffineOpen_U1
  have h1 := actual_cover_open_nonempty K _ _
    ((sup_comm _ _).trans (actualTwoAffineOpenCover K).sup_eq_top)
    (actualTwoAffineOpenCover K).isAffineOpen_U0
  exact (_root_.AlgebraicCurve.nonempty_linearEquiv_cechH0_and_cechH1
    (actualTwoAffineOpenCover K) (curveToBase K) h0 h1).2

theorem actual_placeCechH1_finrank : Module.finrank K (actualPlaceCechH1 K) = 2 := by
  obtain ⟨e⟩ := actual_structureSheaf_placeCechH1_equiv K
  exact e.finrank_eq.symm.trans (actual_structureSheaf_cechH1_finrank K)

theorem actual_globalH1_finrank_of_genusReached
    [IsCurveOver K (actualCurveFunctionField K)]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K (actualCurveFunctionField K)))]
    {γ : ℤ} {D₀ : Divisor K (actualCurveFunctionField K)}
    (h : RiemannGenusReachedAt γ D₀) :
    Module.finrank K (H1 (0 : Divisor K (actualCurveFunctionField K))) = 2 := by
  obtain ⟨hcover, h₀, h₁⟩ := actual_places_cover_nonempty_complements K
  let e : actualPlaceCechH1 K ≃ₗ[K] H1 (0 : Divisor K (actualCurveFunctionField K)) :=
    LinearEquiv.ofBijective (cechH1ToH1 hcover 0)
      (cechH1ToH1_bijective h hcover h₀ h₁ 0)
  exact e.finrank_eq.symm.trans (actual_placeCechH1_finrank K)

instance actualFunctionFieldEssFiniteType :
    Algebra.EssFiniteType K (actualCurveFunctionField K) :=
  _root_.AlgebraicCurve.essFiniteType_functionField (curveToBase K)

def actualPositiveInfinitySection : Spec (.of K) ⟶ curveScheme K :=
  Order13MixedQuadraticInfinitySections.infinitySectionZero K

theorem actualPositiveInfinitySection_over_base :
    actualPositiveInfinitySection K ≫ curveToBase K = 𝟙 _ :=
  Order13MixedQuadraticInfinitySections.infinitySectionZero_comp K

theorem actualPositiveInfinityPoint_isClosed :
    IsClosed ({(actualPositiveInfinitySection K).base (IsLocalRing.closedPoint K)} : Set (curveScheme K)) := by
  haveI : IsClosedImmersion (actualPositiveInfinitySection K ≫ curveToBase K) := by
    rw [actualPositiveInfinitySection_over_base]
    infer_instance
  haveI : IsClosedImmersion (actualPositiveInfinitySection K) :=
    IsClosedImmersion.of_comp (actualPositiveInfinitySection K) (curveToBase K)
  have h := (actualPositiveInfinitySection K).isClosedEmbedding.isClosedMap
    {IsLocalRing.closedPoint K} isClosed_singleton
  convert h using 1
  ext x
  constructor
  · intro hx
    refine ⟨IsLocalRing.closedPoint K, Set.mem_singleton _, ?_⟩
    exact (Set.mem_singleton_iff.mp hx).symm
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff.mp hy]
    exact Set.mem_singleton _

def actualPositiveInfinityClosedPoint : closedPoints (curveScheme K) :=
  ⟨(actualPositiveInfinitySection K).base (IsLocalRing.closedPoint K),
    mem_closedPoints_iff.mpr (actualPositiveInfinityPoint_isClosed K)⟩

def actualPositiveInfinityPlace : Place K (actualCurveFunctionField K) :=
  actualPlaceOfPoint K (actualPositiveInfinityClosedPoint K)

theorem actualPositiveInfinityPlace_isRational : (actualPositiveInfinityPlace K).IsRational :=
  Place.isRational_of_range_stalk_section_eq (curveToBase K)
    (actualPositiveInfinitySection K) (actualPositiveInfinitySection_over_base K)
    (actualPositiveInfinityPlace K) (actualPlaceOfPoint_stalk_range K (actualPositiveInfinityClosedPoint K))

theorem actualPositiveInfinityPlace_deg : (actualPositiveInfinityPlace K).deg = 1 :=
  ((actualPositiveInfinityPlace K).isRational_iff_deg_eq_one).mp (actualPositiveInfinityPlace_isRational K)

theorem actual_constantsAreBase_mixed_dyadic_fibre : ConstantsAreBase K (actualCurveFunctionField K) :=
  constantsAreBase_of_deg_eq_one (actualPositiveInfinityPlace K) (actualPositiveInfinityPlace_deg K)

theorem actual_stichtenothGenusExists_mixed_dyadic_fibre :
    StichtenothGenusExists K (actualCurveFunctionField K) :=
  stichtenothGenusExists_of_isCurveOver (actual_constantsAreBase_mixed_dyadic_fibre K)

theorem actual_genusFF_eq_two_mixed_dyadic_fibre : genusFF K (actualCurveFunctionField K) = 2 := by
  obtain ⟨_, hfinite, γ, D₀, hgenus⟩ := actual_stichtenothGenusExists_mixed_dyadic_fibre K
  letI := hfinite
  exact actual_globalH1_finrank_of_genusReached K hgenus


end MazurTransfer.Order13MixedDyadicFibreGenus
#print axioms MazurTransfer.Order13MixedDyadicFibreGenus.actual_genusFF_eq_two_mixed_dyadic_fibre

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every geometric fibre of the actual dyadic mixed family
has the original genus-two CurveModel and Riemann-Roch formula.
Named downstream consumer: the same family's six-section Picard chart criterion.
Reuses official Anthropic FLT Riemann-Roch at its retained exact pin.
-/

noncomputable section
namespace MazurTransfer.Order13MixedDyadicFibreGenusTwoModels
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedDyadicFibreCurveModel Order13MixedDyadicFibreGenus
open Order13MixedQuadraticActualCurveBaseChange
local instance instFactPrimeOfNatNat_order13MixedDyadicFibreGenusTwoModels : Fact (Nat.Prime 2) := ⟨by decide⟩
variable (K : Type) [Field K] [Algebra BaseRing K] [PerfectField K]

theorem actual_genus_two_riemannRoch [IsAlgClosed K] :
    ∃ Kc : Divisor K (actualCurveFunctionField K),
      ∀ D : Divisor K (actualCurveFunctionField K),
        (ell D : ℤ) - ell (Kc-D) = Divisor.degree D + 1 - 2 := by
  obtain ⟨Kc,g,hRR⟩ := exists_canonicalDivisor_genus_riemannRoch K (actualCurveFunctionField K)
  have hg := eq_genusFF_of_forall_ell_sub_ell_eq
    (actual_constantsAreBase_mixed_dyadic_fibre K) hRR
  rw [actual_genusFF_eq_two_mixed_dyadic_fibre K] at hg
  refine ⟨Kc, ?_⟩
  simpa only [hg, Nat.cast_ofNat] using hRR


theorem geometric_fibre_genus_two_models
    (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (.of k) ⟶ Spec (.of BaseRing)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L) (_ : IsCurveOver k L)
      (M : CurveModel k L) (e : M.C ≅ pullback (curveToBase BaseRing) s)
      (he : e.hom ≫ pullback.snd (curveToBase BaseRing) s = M.toBase)
      (Kc : Divisor k L),
      ∀ D : Divisor k L, (ell D : ℤ) - ell (Kc-D) = Divisor.degree D + 1 - 2 := by
  obtain ⟨φ,rfl⟩ := Spec.map_surjective s
  letI : Algebra BaseRing k := φ.hom.toAlgebra
  obtain ⟨Kc,hRR⟩ := actual_genus_two_riemannRoch k
  refine ⟨actualCurveFunctionField k, inferInstance, inferInstance, inferInstance,
    actualCurveModel k, (wholeCurve_isPullback BaseRing k).isoPullback, ?_, Kc,hRR⟩
  exact (wholeCurve_isPullback BaseRing k).isoPullback_hom_snd

end MazurTransfer.Order13MixedDyadicFibreGenusTwoModels
#print axioms MazurTransfer.Order13MixedDyadicFibreGenusTwoModels.geometric_fibre_genus_two_models

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: all 216 ordered triples of the six literal mixed sections
satisfy the original Picard HasChartSections over Z localized at two.
Named downstream consumer: actual dyadic mixed Picard representability.
-/

noncomputable section
namespace MazurTransfer.Order13ActualDyadicMixedPicardChartSections
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedIntegralSections MixedOriginalDyadicSixSectionPicardChartCriterion20261019
local instance instFactPrimeOfNatNat_order13ActualDyadicMixedPicardChartSections : Fact (Nat.Prime 2) := ⟨by decide⟩

def actualTripleFamily := tripleFamily (curveToBase BaseRing) (sixMarkedSections BaseRing)

theorem actual_hasChartSections :
    HasChartSections (curveToBase BaseRing) (g := 2) (r := 5) actualTripleFamily :=
  hasChartSections_of_six_sections (curveToBase BaseRing) (sixMarkedSections BaseRing)
    (fun k _ _ s => Order13MixedSixMarkedSectionsDistinct.six_sections_field_precomposition_injective BaseRing k s)
    (fun k _ _ s => Order13MixedDyadicFibreGenusTwoModels.geometric_fibre_genus_two_models k s)

end MazurTransfer.Order13ActualDyadicMixedPicardChartSections
#print axioms MazurTransfer.Order13ActualDyadicMixedPicardChartSections.actual_hasChartSections

end


