-- Prove2me | Definitions.Def_MazurTransfer_Order13CubicPrincipalDivisorAndCuspClassOriginalDataAndCertificatesExplicitPlaceSurjectivityV220261018
-- name    : MazurTransfer_Order13CubicPrincipalDivisorAndCuspClassOriginalDataAndCertificatesExplicitPlaceSurjectivityV220261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T19:26:26.606008+00:00
-- url     : https://prove2.me/theorems/3b504866-0e86-4c6a-a1d8-59f327a00a53
-- title:
--   Original cubic principal divisors and cusp-class relation
-- statement:
--   Retain the exact cubic orders at the six marked cusp places, vanishing orders away from them, both complete principal divisors, and the original relation 3B − C = 2A among the cusp-difference classes. All forty-nine complete original declaration types and thirteen whole nonproof values are compared, together with eight complete original field and tangent fact-provider types. Named downstream consumers are cubic place-order characterization and the infinity-class diamond eigenvalue. Place surjectivity is proved from the accepted closed-point/stalk-range theorem with every original hypothesis retained.
-- source:
--   Retained original MazurTheorem cubic and diamond-orbit modules, Apache-2.0, Vas and contributors. Complete original declaration types and whole nonproof constructor values are compared. These interfaces package original data and proved certificates; they add no arithmetic assumption or new owned theorem-acceptance credit.

import Mathlib
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Definitions.Def_MazurTransfer_Order13CubicCuspLocalOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13OrdinaryFunctionFieldAndCuspCentersOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13CubicActualFunctionFieldOriginalDataAndCertificatesSinglePublicUniformizerContextV320261018
import Definitions.Def_MazurTransfer_Order13InfinityDivisorClassData
import Theorems.Thm_MazurTransfer_order13_ordinary_chart_or_two_infinity_centers
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldNaturality_coordinate_embedding_via_stalk
import Theorems.Thm_MazurTransfer_PlaceOrderOfRangeUnit_ord_image_unit
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original exact cubic orders at the six marked cusps, absence of other support, the two complete cubic principal divisors, and the relation 3B-C=2A among the original cusp-difference classes. Named downstream consumers: Order13CubicPlaceOrderCharacterization and the infinity-class diamond eigenvalue. All original data and hypotheses are retained; the chart complement uses its accepted minimal statement interface.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact orders of both cubic functions at all four literal
ordinary cusp places. Named downstream consumer: the complete cubic
principal divisor on the actual rational curve.
-/

noncomputable section
namespace MazurTransfer.Order13CubicActualCuspValuations
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13IntegralSections Order13RationalSectionPicardInjection
open Order13OrdinaryLocalParameter Order13OrdinaryChartActualFunctionField
open Order13OrdinaryActualPlaceOrders Order13ActualOrdinaryPlaceCenters
open Order13CubicCuspLocalOrders
open Order13CubicActualInfinityValuations Order13CubicActualOrdinaryChart
local instance order13CubicActualCuspValuationsOriginalFactProvider120261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance order13CubicActualCuspValuationsOriginalFactProvider220261018 : Fact (2 * (1 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance order13CubicActualCuspValuationsOriginalFactProvider320261018 : Fact (2 * (-1 : ℚ) ≠ 0) := ⟨by norm_num⟩

def zeroPositivePlace : Place ℚ (actualCurveFunctionField ℚ) :=
  actualPlaceOfPoint ℚ (sectionClosedPoint ℚ (zeroPositiveSection ℚ))

theorem ordinaryPlace_eq_zeroPositive : ordinaryPlace 0 1 (zeroPositiveProof ℚ) = zeroPositivePlace :=
  ordinaryPlace_eq_actualPlaceOfPoint 0 1 (zeroPositiveProof ℚ)

def zeroNegativePlace : Place ℚ (actualCurveFunctionField ℚ) :=
  actualPlaceOfPoint ℚ (sectionClosedPoint ℚ (zeroNegativeSection ℚ))

theorem ordinaryPlace_eq_zeroNegative : ordinaryPlace 0 (-1) (zeroNegativeProof ℚ) = zeroNegativePlace :=
  ordinaryPlace_eq_actualPlaceOfPoint 0 (-1) (zeroNegativeProof ℚ)

def negOnePositivePlace : Place ℚ (actualCurveFunctionField ℚ) :=
  actualPlaceOfPoint ℚ (sectionClosedPoint ℚ (negOnePositiveSection ℚ))

theorem ordinaryPlace_eq_negOnePositive : ordinaryPlace (-1) 1 (negOnePositiveProof ℚ) = negOnePositivePlace :=
  ordinaryPlace_eq_actualPlaceOfPoint (-1) 1 (negOnePositiveProof ℚ)

def negOneNegativePlace : Place ℚ (actualCurveFunctionField ℚ) :=
  actualPlaceOfPoint ℚ (sectionClosedPoint ℚ (negOneNegativeSection ℚ))

theorem ordinaryPlace_eq_negOneNegative : ordinaryPlace (-1) (-1) (negOneNegativeProof ℚ) = negOneNegativePlace :=
  ordinaryPlace_eq_actualPlaceOfPoint (-1) (-1) (negOneNegativeProof ℚ)

theorem cubicMinusFunction_ord_at_zeroPositive : zeroPositivePlace.ord cubicMinusFunction = 3 := by
  rw [← ordinaryPlace_eq_zeroPositive, cubicMinusFunction_eq_ordinaryMinus, ← localEmbedding_coordinate ℚ 0 1 (zeroPositiveProof ℚ)]
  exact ordinaryPlace_ord_associated_parameter_pow _ _ _ _ 3 (Order13CubicCuspPublicCompatibility.minus_at_zeroPositive_associated)

theorem cubicPlusFunction_ord_at_zeroPositive : zeroPositivePlace.ord cubicPlusFunction = 0 := by
  rw [← ordinaryPlace_eq_zeroPositive, cubicPlusFunction_eq_ordinaryPlus, ← localEmbedding_coordinate ℚ 0 1 (zeroPositiveProof ℚ)]
  exact ordinaryPlace_ord_isUnit _ _ _ _ (plus_isUnit_at_zeroPositive ℚ)

theorem cubicMinusFunction_ord_at_zeroNegative : zeroNegativePlace.ord cubicMinusFunction = 0 := by
  rw [← ordinaryPlace_eq_zeroNegative, cubicMinusFunction_eq_ordinaryMinus, ← localEmbedding_coordinate ℚ 0 (-1) (zeroNegativeProof ℚ)]
  exact ordinaryPlace_ord_isUnit _ _ _ _ (minus_isUnit_at_zeroNegative ℚ)

theorem cubicPlusFunction_ord_at_zeroNegative : zeroNegativePlace.ord cubicPlusFunction = 3 := by
  rw [← ordinaryPlace_eq_zeroNegative, cubicPlusFunction_eq_ordinaryPlus, ← localEmbedding_coordinate ℚ 0 (-1) (zeroNegativeProof ℚ)]
  exact ordinaryPlace_ord_associated_parameter_pow _ _ _ _ 3 (Order13CubicCuspPublicCompatibility.plus_at_zeroNegative_associated)

theorem cubicMinusFunction_ord_at_negOnePositive : negOnePositivePlace.ord cubicMinusFunction = 0 := by
  rw [← ordinaryPlace_eq_negOnePositive, cubicMinusFunction_eq_ordinaryMinus, ← localEmbedding_coordinate ℚ (-1) 1 (negOnePositiveProof ℚ)]
  exact ordinaryPlace_ord_isUnit _ _ _ _ (minus_isUnit_at_negOnePositive ℚ)

theorem cubicPlusFunction_ord_at_negOnePositive : negOnePositivePlace.ord cubicPlusFunction = 1 := by
  rw [← ordinaryPlace_eq_negOnePositive, cubicPlusFunction_eq_ordinaryPlus, ← localEmbedding_coordinate ℚ (-1) 1 (negOnePositiveProof ℚ)]
  exact ordinaryPlace_ord_associated_parameter_pow _ _ _ _ 1 (Order13CubicCuspPublicCompatibility.plus_at_negOnePositive_associated)

theorem cubicMinusFunction_ord_at_negOneNegative : negOneNegativePlace.ord cubicMinusFunction = 1 := by
  rw [← ordinaryPlace_eq_negOneNegative, cubicMinusFunction_eq_ordinaryMinus, ← localEmbedding_coordinate ℚ (-1) (-1) (negOneNegativeProof ℚ)]
  exact ordinaryPlace_ord_associated_parameter_pow _ _ _ _ 1 (Order13CubicCuspPublicCompatibility.minus_at_negOneNegative_associated)

theorem cubicPlusFunction_ord_at_negOneNegative : negOneNegativePlace.ord cubicPlusFunction = 0 := by
  rw [← ordinaryPlace_eq_negOneNegative, cubicPlusFunction_eq_ordinaryPlus, ← localEmbedding_coordinate ℚ (-1) (-1) (negOneNegativeProof ℚ)]
  exact ordinaryPlace_ord_isUnit _ _ _ _ (plus_isUnit_at_negOneNegative ℚ)

end MazurTransfer.Order13CubicActualCuspValuations
#print axioms MazurTransfer.Order13CubicActualCuspValuations.cubicMinusFunction_ord_at_zeroPositive
#print axioms MazurTransfer.Order13CubicActualCuspValuations.cubicMinusFunction_ord_at_negOneNegative
#print axioms MazurTransfer.Order13CubicActualCuspValuations.cubicPlusFunction_ord_at_zeroNegative
#print axioms MazurTransfer.Order13CubicActualCuspValuations.cubicPlusFunction_ord_at_negOnePositive

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both cubic functions have order zero at ordinary-chart
places where x and x+1 are nonzero in the residue field. Named downstream
consumer: exclusion of noncusp support in the cubic principal divisor.
-/

noncomputable section
namespace MazurTransfer.Order13CubicOrdinaryPlaceOrders
open AlgebraicGeometry CategoryTheory AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13CubicNormChartCertificate Order13CubicActualOrdinaryChart
local instance order13CubicOrdinaryPlaceOrdersOriginalFactProvider120261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem ordinary_factors_stalk_units (p : Spec (.of (CoordinateRing ℚ)))
    (hx : xCoordinate ℚ ∉ p.asIdeal) (hx1 : xCoordinate ℚ + 1 ∉ p.asIdeal) :
    IsUnit ((StructureSheaf.toStalk (CoordinateRing ℚ) p).hom (ordinaryMinus ℚ)) ∧
    IsUnit ((StructureSheaf.toStalk (CoordinateRing ℚ) p).hom (ordinaryPlus ℚ)) := by
  let := StructureSheaf.stalkAlgebra (CoordinateRing ℚ) p
  let := StructureSheaf.IsLocalization.to_stalk (CoordinateRing ℚ) p
  haveI : p.asIdeal.IsPrime := p.isPrime
  let f := (StructureSheaf.toStalk (CoordinateRing ℚ) p).hom
  have hu : IsUnit (f (xCoordinate ℚ)) := (IsLocalization.AtPrime.isUnit_to_map_iff (R := CoordinateRing ℚ) ((Spec.structureSheaf (CoordinateRing ℚ)).presheaf.stalk p) p.asIdeal _).mpr hx
  have hu1 : IsUnit (f (xCoordinate ℚ + 1)) := (IsLocalization.AtPrime.isUnit_to_map_iff (R := CoordinateRing ℚ) ((Spec.structureSheaf (CoordinateRing ℚ)).presheaf.stalk p) p.asIdeal _).mpr hx1
  have h4 : IsUnit (f (-4)) := by
    have h := (isUnit_iff_ne_zero.mpr (by norm_num : (-4 : ℚ) ≠ 0)).map
      (f.comp (algebraMap ℚ (CoordinateRing ℚ)))
    simpa only [RingHom.comp_apply, map_neg, map_ofNat] using h
  have hprod : IsUnit (f (ordinaryMinus ℚ) * f (ordinaryPlus ℚ)) := by
    rw [← map_mul, ordinary_product, map_mul, map_mul, map_pow]
    exact (h4.mul (hu.pow 3)).mul hu1
  exact ⟨isUnit_of_mul_isUnit_left hprod, isUnit_of_mul_isUnit_right hprod⟩

theorem ordinaryFunction_ord_of_stalk_unit (b : CoordinateRing ℚ)
    (p : Spec (.of (CoordinateRing ℚ)))
    (x : closedPoints (curveScheme ℚ)) (hx : ordinaryChartMap ℚ p = x.1)
    (hb : IsUnit ((StructureSheaf.toStalk (CoordinateRing ℚ) p).hom b)) :
    (actualPlaceOfPoint ℚ x).ord (algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ) b) = 0 := by
  let c := (asIso ((ordinaryChartMap ℚ).stalkMap p)).inv.hom
    ((StructureSheaf.toStalk (CoordinateRing ℚ) p).hom b)
  have hc : IsUnit c := hb.map ((asIso ((ordinaryChartMap ℚ).stalkMap p)).inv.hom)
  have H := congrArg (fun f => f.hom b)
    (AffineOpenChartFunctionFieldNaturality.coordinate_embedding_via_stalk
      (.of (CoordinateRing ℚ)) (ordinaryChartMap ℚ) p)
  have Hrange :
      (algebraMap ((curveScheme ℚ).presheaf.stalk (ordinaryChartMap ℚ p))
        (actualCurveFunctionField ℚ)).range = (actualPlaceOfPoint ℚ x).toValuationSubring.toSubring := by
    rw [hx]
    exact actualPlaceOfPoint_stalk_range ℚ x
  change (actualPlaceOfPoint ℚ x).ord
    (AffineOpenChartFunctionField.coordinateEmbedding (.of (CoordinateRing ℚ)) (ordinaryChartMap ℚ) b) = 0
  change AffineOpenChartFunctionField.coordinateEmbedding (.of (CoordinateRing ℚ))
    (ordinaryChartMap ℚ) b =
    algebraMap ((curveScheme ℚ).presheaf.stalk (ordinaryChartMap ℚ p)) (actualCurveFunctionField ℚ) c at H
  rw [H]
  exact PlaceOrderOfRangeUnit.ord_image_unit ℚ (actualCurveFunctionField ℚ)
    ((curveScheme ℚ).presheaf.stalk (ordinaryChartMap ℚ p)) (actualPlaceOfPoint ℚ x)
    (algebraMap _ _) Hrange c hc

theorem cubicFunctions_ord_at_ordinary_point
    (p : Spec (.of (CoordinateRing ℚ)))
    (x : closedPoints (curveScheme ℚ)) (hp : ordinaryChartMap ℚ p = x.1)
    (hx : xCoordinate ℚ ∉ p.asIdeal) (hx1 : xCoordinate ℚ + 1 ∉ p.asIdeal) :
    (actualPlaceOfPoint ℚ x).ord Order13CubicActualInfinityValuations.cubicMinusFunction = 0 ∧
    (actualPlaceOfPoint ℚ x).ord Order13CubicActualInfinityValuations.cubicPlusFunction = 0 := by
  rw [cubicMinusFunction_eq_ordinaryMinus, cubicPlusFunction_eq_ordinaryPlus]
  have hu := ordinary_factors_stalk_units p hx hx1
  exact ⟨ordinaryFunction_ord_of_stalk_unit _ p x hp hu.1,
    ordinaryFunction_ord_of_stalk_unit _ p x hp hu.2⟩

end MazurTransfer.Order13CubicOrdinaryPlaceOrders
#print axioms MazurTransfer.Order13CubicOrdinaryPlaceOrders.cubicFunctions_ord_at_ordinary_point

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the six literal marked places are pairwise distinct and
the cubic function orders at each are explicit. Named downstream consumer:
cubic principal-divisor coefficient equality.
-/

noncomputable section
namespace MazurTransfer.Order13CubicMarkedPlaceOrders
open AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13CubicActualInfinityValuations Order13CubicActualCuspValuations
open Order13PellPrincipalDivisor (positivePlace negativePlace)
open Order13IntegralSections Order13RationalSectionPicardInjection Order13ActualInfinityPlaceCenters
local instance order13CubicMarkedPlaceOrdersOriginalFactProvider120261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem positivePlace_ord_minus : positivePlace.ord cubicMinusFunction = -1 := by
  rw [positivePlace, positiveInfinitySection, ← infinityPlace_eq_actualPlaceOfPoint 1 (Order13CubicInfinityLocalOrders.positiveProof ℚ)]
  exact cubicMinusFunction_ord_at_positive

theorem negativePlace_ord_minus : negativePlace.ord cubicMinusFunction = -3 := by
  rw [negativePlace, negativeInfinitySection, ← infinityPlace_eq_actualPlaceOfPoint (-1) (Order13CubicInfinityLocalOrders.negativeProof ℚ)]
  exact cubicMinusFunction_ord_at_negative

theorem positivePlace_ord_plus : positivePlace.ord cubicPlusFunction = -3 := by
  rw [positivePlace, positiveInfinitySection, ← infinityPlace_eq_actualPlaceOfPoint 1 (Order13CubicInfinityLocalOrders.positiveProof ℚ)]
  exact cubicPlusFunction_ord_at_positive

theorem negativePlace_ord_plus : negativePlace.ord cubicPlusFunction = -1 := by
  rw [negativePlace, negativeInfinitySection, ← infinityPlace_eq_actualPlaceOfPoint (-1) (Order13CubicInfinityLocalOrders.negativeProof ℚ)]
  exact cubicPlusFunction_ord_at_negative

def markedPlace : Fin 6 → Place ℚ (actualCurveFunctionField ℚ) :=
  ![positivePlace, negativePlace, zeroPositivePlace, zeroNegativePlace, negOnePositivePlace, negOneNegativePlace]
def minusOrders : Fin 6 → ℤ := ![-1, -3, 3, 0, 0, 1]
def plusOrders : Fin 6 → ℤ := ![-3, -1, 0, 3, 1, 0]

theorem markedPlace_minus_order (i : Fin 6) : (markedPlace i).ord cubicMinusFunction = minusOrders i := by
  fin_cases i <;> norm_num [markedPlace, minusOrders,
    positivePlace_ord_minus, negativePlace_ord_minus, cubicMinusFunction_ord_at_zeroPositive,
    cubicMinusFunction_ord_at_zeroNegative, cubicMinusFunction_ord_at_negOnePositive, cubicMinusFunction_ord_at_negOneNegative]

theorem markedPlace_plus_order (i : Fin 6) : (markedPlace i).ord cubicPlusFunction = plusOrders i := by
  fin_cases i <;> norm_num [markedPlace, plusOrders,
    positivePlace_ord_plus, negativePlace_ord_plus, cubicPlusFunction_ord_at_zeroPositive,
    cubicPlusFunction_ord_at_zeroNegative, cubicPlusFunction_ord_at_negOnePositive, cubicPlusFunction_ord_at_negOneNegative]

theorem markedPlace_injective : Function.Injective markedPlace := by
  intro i j hij
  have hm := congrArg (fun v : Place ℚ (actualCurveFunctionField ℚ) => v.ord cubicMinusFunction) hij
  have hp := congrArg (fun v : Place ℚ (actualCurveFunctionField ℚ) => v.ord cubicPlusFunction) hij
  rw [markedPlace_minus_order, markedPlace_minus_order] at hm
  rw [markedPlace_plus_order, markedPlace_plus_order] at hp
  fin_cases i <;> fin_cases j <;> norm_num [minusOrders, plusOrders] at *

end MazurTransfer.Order13CubicMarkedPlaceOrders
#print axioms MazurTransfer.Order13CubicMarkedPlaceOrders.markedPlace_injective

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: neither cubic function has nonzero order outside the six
literal marked cusp places. Named downstream consumer: complete cubic
principal-divisor equality on the actual rational curve.
-/

noncomputable section
namespace MazurTransfer.Order13CubicGlobalSupport
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13IntegralSections Order13RationalSectionPicardInjection
open Order13CubicActualInfinityValuations Order13CubicActualCuspValuations
open Order13ActualInfinityPlaceCenters
open Order13PellPrincipalDivisor (positivePlace negativePlace)
open Order13OrdinaryCuspCenters Order13CubicOrdinaryPlaceOrders
local instance order13CubicGlobalSupportOriginalFactProvider120261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem cubicFunctions_ord_away_marked_places (v : Place ℚ (actualCurveFunctionField ℚ))
    (hip : v ≠ positivePlace) (hin : v ≠ negativePlace)
    (h0p : v ≠ zeroPositivePlace) (h0n : v ≠ zeroNegativePlace)
    (h1p : v ≠ negOnePositivePlace) (h1n : v ≠ negOneNegativePlace) :
    v.ord cubicMinusFunction = 0 ∧ v.ord cubicPlusFunction = 0 := by
  have hsurj : Function.Surjective (actualPlaceOfPoint ℚ) := by
    intro w
    obtain ⟨x, hx, hrange⟩ :=
      _root_.AlgebraicCurve.exists_closedPoint_range_stalk_eq (curveToBase ℚ) w
    refine ⟨⟨x, mem_closedPoints_iff.mpr hx⟩, Place.ext ?_⟩
    apply ValuationSubring.toSubring_injective
    rw [← actualPlaceOfPoint_stalk_range, hrange]
  obtain ⟨x, rfl⟩ := hsurj v
  rcases MazurTransfer.order13_ordinary_chart_or_two_infinity_centers x.1 with hx | hx | hx
  · obtain ⟨p, hp⟩ := hx
    have hxp : xCoordinate ℚ ∉ p.asIdeal := by
      intro h
      rcases point_with_zero_x p h with h | h
      · apply h0p
        apply congrArg (actualPlaceOfPoint ℚ)
        exact Subtype.ext (hp.symm.trans h)
      · apply h0n
        apply congrArg (actualPlaceOfPoint ℚ)
        exact Subtype.ext (hp.symm.trans h)
    have hx1p : xCoordinate ℚ + 1 ∉ p.asIdeal := by
      intro h
      rcases point_with_neg_one_x p h with h | h
      · apply h1p
        apply congrArg (actualPlaceOfPoint ℚ)
        exact Subtype.ext (hp.symm.trans h)
      · apply h1n
        apply congrArg (actualPlaceOfPoint ℚ)
        exact Subtype.ext (hp.symm.trans h)
    exact cubicFunctions_ord_at_ordinary_point p x hp hxp hx1p
  · exfalso
    apply hip
    apply congrArg (actualPlaceOfPoint ℚ)
    exact Subtype.ext (hx.trans (infinity_section_center 1 (Order13PellInfinityLocalOrders.positiveProof ℚ)).symm)
  · exfalso
    apply hin
    apply congrArg (actualPlaceOfPoint ℚ)
    exact Subtype.ext (hx.trans (infinity_section_center (-1) (Order13PellInfinityLocalOrders.negativeProof ℚ)).symm)

end MazurTransfer.Order13CubicGlobalSupport
#print axioms MazurTransfer.Order13CubicGlobalSupport.cubicFunctions_ord_away_marked_places

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: complete principal divisors of y-g(x) and y+g(x) in the
actual rational scheme function field, supported on the six literal cusps.
Named downstream consumer: the infinity-class relation for actual norm
kernel identification.
-/

noncomputable section
namespace MazurTransfer.Order13CubicPrincipalDivisors
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13CubicActualInfinityValuations Order13CubicActualOrdinaryChart
open Order13CubicMarkedPlaceOrders Order13CubicGlobalSupport
local instance order13CubicPrincipalDivisorsOriginalFactProvider120261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

noncomputable def cubicMinusDivisor : Divisor ℚ (actualCurveFunctionField ℚ) :=
  ∑ i : Fin 6, Finsupp.single (markedPlace i) (minusOrders i)
noncomputable def cubicPlusDivisor : Divisor ℚ (actualCurveFunctionField ℚ) :=
  ∑ i : Fin 6, Finsupp.single (markedPlace i) (plusOrders i)

theorem cubicMinusDivisor_at_marked (i : Fin 6) : cubicMinusDivisor (markedPlace i) = minusOrders i := by
  classical
  simp [cubicMinusDivisor, Finsupp.single_apply, markedPlace_injective.eq_iff]

theorem cubicPlusDivisor_at_marked (i : Fin 6) : cubicPlusDivisor (markedPlace i) = plusOrders i := by
  classical
  simp [cubicPlusDivisor, Finsupp.single_apply, markedPlace_injective.eq_iff]

theorem cubicFunctions_ord_away_range (v : Place ℚ (actualCurveFunctionField ℚ))
    (hv : v ∉ Set.range markedPlace) : v.ord cubicMinusFunction = 0 ∧ v.ord cubicPlusFunction = 0 := by
  have hneq (i : Fin 6) : v ≠ markedPlace i := fun h => hv ⟨i, h.symm⟩
  exact cubicFunctions_ord_away_marked_places v (hneq 0) (hneq 1) (hneq 2) (hneq 3) (hneq 4) (hneq 5)

theorem cubicMinusDivisor_coefficient (v : Place ℚ (actualCurveFunctionField ℚ)) :
    cubicMinusDivisor v = v.ord cubicMinusFunction := by
  classical
  by_cases hv : v ∈ Set.range markedPlace
  · obtain ⟨i, rfl⟩ := hv
    rw [cubicMinusDivisor_at_marked, markedPlace_minus_order]
  · rw [(cubicFunctions_ord_away_range v hv).1]
    have hneq (i : Fin 6) : markedPlace i ≠ v := fun h => hv ⟨i, h⟩
    simp [cubicMinusDivisor, Finsupp.single_apply, hneq]

theorem cubicPlusDivisor_coefficient (v : Place ℚ (actualCurveFunctionField ℚ)) :
    cubicPlusDivisor v = v.ord cubicPlusFunction := by
  classical
  by_cases hv : v ∈ Set.range markedPlace
  · obtain ⟨i, rfl⟩ := hv
    rw [cubicPlusDivisor_at_marked, markedPlace_plus_order]
  · rw [(cubicFunctions_ord_away_range v hv).2]
    have hneq (i : Fin 6) : markedPlace i ≠ v := fun h => hv ⟨i, h⟩
    simp [cubicPlusDivisor, Finsupp.single_apply, hneq]

theorem cubicMinusDivisor_isPrincipal : Divisor.IsPrincipal cubicMinusDivisor :=
  ⟨cubicMinusFunction, cubicMinusFunction_ne_zero, cubicMinusDivisor_coefficient⟩

theorem cubicPlusDivisor_isPrincipal : Divisor.IsPrincipal cubicPlusDivisor :=
  ⟨cubicPlusFunction, cubicPlusFunction_ne_zero, cubicPlusDivisor_coefficient⟩

end MazurTransfer.Order13CubicPrincipalDivisors
#print axioms MazurTransfer.Order13CubicPrincipalDivisors.cubicMinusDivisor_isPrincipal
#print axioms MazurTransfer.Order13CubicPrincipalDivisors.cubicPlusDivisor_isPrincipal

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the complete cubic principal divisors give the exact
arithmetic Picard relation 3B-C=2A between the three cusp differences.
Named downstream consumer: infinity-class diamond eigenvalue and norm
kernel identification.
-/

noncomputable section
namespace MazurTransfer.Order13CubicPicardClassRelation
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13IntegralSections Order13RationalSectionPicardInjection
open Order13CubicActualCuspValuations Order13CubicMarkedPlaceOrders
open Order13PellPrincipalDivisor (positivePlace negativePlace)
open Order13InfinityPicardClassOrder Order13CubicPrincipalDivisors
local instance order13CubicPicardClassRelationOriginalFactProvider120261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem zeroPositivePlace_deg : zeroPositivePlace.deg = 1 :=
  (sectionDegreeOneClosedPoint ℚ (zeroPositiveSection ℚ)).2
theorem zeroNegativePlace_deg : zeroNegativePlace.deg = 1 :=
  (sectionDegreeOneClosedPoint ℚ (zeroNegativeSection ℚ)).2
theorem negOnePositivePlace_deg : negOnePositivePlace.deg = 1 :=
  (sectionDegreeOneClosedPoint ℚ (negOnePositiveSection ℚ)).2
theorem negOneNegativePlace_deg : negOneNegativePlace.deg = 1 :=
  (sectionDegreeOneClosedPoint ℚ (negOneNegativeSection ℚ)).2

def zeroDifferenceDivisor : Divisor.degZero (K := ℚ) (F := actualCurveFunctionField ℚ) :=
  ⟨Finsupp.single zeroPositivePlace 1 - Finsupp.single zeroNegativePlace 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
      zeroPositivePlace_deg, zeroNegativePlace_deg]
    norm_num⟩

def negOneDifferenceDivisor : Divisor.degZero (K := ℚ) (F := actualCurveFunctionField ℚ) :=
  ⟨Finsupp.single negOnePositivePlace 1 - Finsupp.single negOneNegativePlace 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
      negOnePositivePlace_deg, negOneNegativePlace_deg]
    norm_num⟩

def zeroClass : Pic0 ℚ (actualCurveFunctionField ℚ) := Pic0.mk zeroDifferenceDivisor
def negOneClass : Pic0 ℚ (actualCurveFunctionField ℚ) := Pic0.mk negOneDifferenceDivisor

theorem cubic_divisor_difference :
    (((3 : ℤ) • zeroDifferenceDivisor - negOneDifferenceDivisor - (2 : ℤ) • infinityDifferenceDivisor :
      Divisor.degZero (K := ℚ) (F := actualCurveFunctionField ℚ)) : Divisor ℚ (actualCurveFunctionField ℚ)) =
      cubicMinusDivisor - cubicPlusDivisor := by
  change (3 : ℤ) • (Finsupp.single zeroPositivePlace 1 - Finsupp.single zeroNegativePlace 1) -
      (Finsupp.single negOnePositivePlace 1 - Finsupp.single negOneNegativePlace 1) -
      (2 : ℤ) • (Finsupp.single negativePlace 1 - Finsupp.single positivePlace 1) = _
  classical
  simp only [cubicMinusDivisor, cubicPlusDivisor, Fin.sum_univ_succ, Fin.sum_univ_zero,
    markedPlace, minusOrders, plusOrders, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finsupp.single_zero, add_zero, zero_add, smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one]
  ext v
  simp only [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> norm_num

theorem three_zeroClass_sub_negOneClass : (3 : ℤ) • zeroClass - negOneClass = (2 : ℤ) • infinityClass := by
  let f := QuotientAddGroup.mk' ((Divisor.principal (K := ℚ) (F := actualCurveFunctionField ℚ)).addSubgroupOf
    (Divisor.degZero (K := ℚ) (F := actualCurveFunctionField ℚ)))
  have Hmem : (3 : ℤ) • zeroDifferenceDivisor - negOneDifferenceDivisor - (2 : ℤ) • infinityDifferenceDivisor ∈
      (Divisor.principal (K := ℚ) (F := actualCurveFunctionField ℚ)).addSubgroupOf
        (Divisor.degZero (K := ℚ) (F := actualCurveFunctionField ℚ)) := by
    change (((3 : ℤ) • zeroDifferenceDivisor - negOneDifferenceDivisor - (2 : ℤ) • infinityDifferenceDivisor :
      Divisor.degZero (K := ℚ) (F := actualCurveFunctionField ℚ)) : Divisor ℚ (actualCurveFunctionField ℚ)) ∈ Divisor.principal
    rw [cubic_divisor_difference]
    exact Divisor.principal.sub_mem cubicMinusDivisor_isPrincipal cubicPlusDivisor_isPrincipal
  have H : f ((3 : ℤ) • zeroDifferenceDivisor - negOneDifferenceDivisor - (2 : ℤ) • infinityDifferenceDivisor) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr Hmem
  rw [map_sub, map_sub, map_zsmul, map_zsmul] at H
  exact sub_eq_zero.mp H

end MazurTransfer.Order13CubicPicardClassRelation
#print axioms MazurTransfer.Order13CubicPicardClassRelation.cubic_divisor_difference
#print axioms MazurTransfer.Order13CubicPicardClassRelation.three_zeroClass_sub_negOneClass


