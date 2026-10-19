-- Prove2me | Definitions.Def_MazurTransfer_Order13CubicActualFunctionFieldOriginalDataAndCertificatesSinglePublicUniformizerContextV320261018
-- name    : MazurTransfer_Order13CubicActualFunctionFieldOriginalDataAndCertificatesSinglePublicUniformizerContextV320261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T19:07:22.495518+00:00
-- url     : https://prove2.me/theorems/02f8efce-b698-4d2d-bc92-e6f318a5bad2
-- title:
--   Original actual cubic functions, infinity orders and ordinary-chart comparison
-- statement:
--   Retain the five original cubic-function constructors on the actual rational function field, their exact infinity orders, and their equality with the ordinary-coordinate cubic functions. All twenty-nine complete original types and all five nonproof values are compared, together with two original field fact-provider types. Named downstream consumers are the actual cusp valuations, global support and cubic principal-divisor calculations.
-- source:
--   Original retained MazurTheorem cubic and local-ring modules, Apache-2.0, Vas and contributors. Complete original declaration types and whole nonproof constructor values are compared. This packages existing checked constructors and their proved certificates; it adds no arithmetic assumption or new theorem acceptance credit.

import Mathlib
import Theorems.Thm_MazurTransfer_Order13PellActualInfinityValuations_infinityPlace_ord_associated_zpow
import Definitions.Def_MazurTransfer_Order13CubicInfinityLocalOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13PellChartOverlapIdentities
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two original cubic functions on the actual rational function field, their infinity orders, and their equality with the literal ordinary-coordinate functions. Named downstream consumers: Order13CubicActualCuspValuations, Order13CubicGlobalSupport and Order13CubicPrincipalDivisors, giving the infinity-class norm eigenvalue. All original data and hypotheses are retained.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal cubic functions in the actual rational scheme
function field have pole orders one and three at the two infinity places.
Named downstream consumer: the complete cusp principal divisor.
-/

noncomputable section
namespace MazurTransfer.Order13CubicActualInfinityValuations
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter Order13ReciprocalChartActualFunctionField
open Order13PellActualInfinityValuations
local instance cubicActualInfinityOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

abbrev normMinus : actualCurveFunctionField ℚ :=
  algebraMap (ReciprocalRing ℚ) (actualCurveFunctionField ℚ)
    (Order13CubicNormChartCertificate.reciprocalMinus ℚ)
abbrev normPlus : actualCurveFunctionField ℚ :=
  algebraMap (ReciprocalRing ℚ) (actualCurveFunctionField ℚ)
    (Order13CubicNormChartCertificate.reciprocalPlus ℚ)
abbrev zField : actualCurveFunctionField ℚ :=
  algebraMap (ReciprocalRing ℚ) (actualCurveFunctionField ℚ) (zCoordinate ℚ)

def cubicMinusFunction : actualCurveFunctionField ℚ := normMinus / zField ^ 3
def cubicPlusFunction : actualCurveFunctionField ℚ := normPlus / zField ^ 3

theorem zField_ne_zero : zField ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    (Order13SingleSectionFiniteAlgebra.actual_reciprocal_z_ne_zero ℚ)

theorem normalizedMinus_ord_at_positive :
    (infinityPlace 1 (Order13CubicInfinityLocalOrders.positiveProof ℚ)).ord normMinus = 2 := by
  rw [normMinus, ← localEmbedding_coordinate ℚ 1 (Order13CubicInfinityLocalOrders.positiveProof ℚ)]
  exact infinityPlace_ord_associated_zpow _ _ _ 2 
    (Order13CubicInfinityLocalOrders.minus_at_positive_associated ℚ (by norm_num))

theorem normalizedMinus_ord_at_negative :
    (infinityPlace (-1) (Order13CubicInfinityLocalOrders.negativeProof ℚ)).ord normMinus = 0 := by
  rw [normMinus, ← localEmbedding_coordinate ℚ (-1) (Order13CubicInfinityLocalOrders.negativeProof ℚ)]
  exact infinityPlace_ord_isUnit _ _ _ 
    (Order13CubicInfinityLocalOrders.minus_isUnit_at_negative ℚ (by norm_num))

theorem normalizedPlus_ord_at_positive :
    (infinityPlace 1 (Order13CubicInfinityLocalOrders.positiveProof ℚ)).ord normPlus = 0 := by
  rw [normPlus, ← localEmbedding_coordinate ℚ 1 (Order13CubicInfinityLocalOrders.positiveProof ℚ)]
  exact infinityPlace_ord_isUnit _ _ _ 
    (Order13CubicInfinityLocalOrders.plus_isUnit_at_positive ℚ (by norm_num))

theorem normalizedPlus_ord_at_negative :
    (infinityPlace (-1) (Order13CubicInfinityLocalOrders.negativeProof ℚ)).ord normPlus = 2 := by
  rw [normPlus, ← localEmbedding_coordinate ℚ (-1) (Order13CubicInfinityLocalOrders.negativeProof ℚ)]
  exact infinityPlace_ord_associated_zpow _ _ _ 2 
    (Order13CubicInfinityLocalOrders.plus_at_negative_associated ℚ (by norm_num))

theorem normMinus_ne_zero : normMinus ≠ 0 := by
  rw [normMinus, ← localEmbedding_coordinate ℚ 1 (Order13CubicInfinityLocalOrders.positiveProof ℚ)]
  apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
  exact (Order13CubicInfinityLocalOrders.minus_at_positive_associated ℚ (by norm_num)).ne_zero_iff.mpr
    (pow_ne_zero 2 (Order13InfinityDiscreteValuationRing.z_ne_zero ℚ 1 (Order13CubicInfinityLocalOrders.positiveProof ℚ)))

theorem normPlus_ne_zero : normPlus ≠ 0 := by
  rw [normPlus, ← localEmbedding_coordinate ℚ (-1) (Order13CubicInfinityLocalOrders.negativeProof ℚ)]
  apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
  exact (Order13CubicInfinityLocalOrders.plus_at_negative_associated ℚ (by norm_num)).ne_zero_iff.mpr
    (pow_ne_zero 2 (Order13InfinityDiscreteValuationRing.z_ne_zero ℚ (-1) (Order13CubicInfinityLocalOrders.negativeProof ℚ)))

theorem ord_div_cube (a : ℚ) (ha : a ^ 2 = 1) (u : actualCurveFunctionField ℚ) (hu : u ≠ 0) :
    (infinityPlace a ha).ord (u / zField ^ 3) = (infinityPlace a ha).ord u - 3 := by
  rw [div_eq_mul_inv, Place.ord_mul _ hu (inv_ne_zero (pow_ne_zero 3 zField_ne_zero)),
    Place.ord_inv, ← zpow_natCast, Place.ord_zpow, infinityPlace_ord_z]
  norm_num [sub_eq_add_neg]

theorem cubicMinusFunction_ord_at_positive :
    (infinityPlace 1 (Order13CubicInfinityLocalOrders.positiveProof ℚ)).ord cubicMinusFunction = -1 := by
  rw [cubicMinusFunction, ord_div_cube _ _ _ normMinus_ne_zero, normalizedMinus_ord_at_positive]
  norm_num

theorem cubicMinusFunction_ord_at_negative :
    (infinityPlace (-1) (Order13CubicInfinityLocalOrders.negativeProof ℚ)).ord cubicMinusFunction = -3 := by
  rw [cubicMinusFunction, ord_div_cube _ _ _ normMinus_ne_zero, normalizedMinus_ord_at_negative]
  norm_num

theorem cubicPlusFunction_ord_at_positive :
    (infinityPlace 1 (Order13CubicInfinityLocalOrders.positiveProof ℚ)).ord cubicPlusFunction = -3 := by
  rw [cubicPlusFunction, ord_div_cube _ _ _ normPlus_ne_zero, normalizedPlus_ord_at_positive]
  norm_num

theorem cubicPlusFunction_ord_at_negative :
    (infinityPlace (-1) (Order13CubicInfinityLocalOrders.negativeProof ℚ)).ord cubicPlusFunction = -1 := by
  rw [cubicPlusFunction, ord_div_cube _ _ _ normPlus_ne_zero, normalizedPlus_ord_at_negative]
  norm_num

end MazurTransfer.Order13CubicActualInfinityValuations
#print axioms MazurTransfer.Order13CubicActualInfinityValuations.cubicMinusFunction_ord_at_positive
#print axioms MazurTransfer.Order13CubicActualInfinityValuations.cubicMinusFunction_ord_at_negative
#print axioms MazurTransfer.Order13CubicActualInfinityValuations.cubicPlusFunction_ord_at_positive
#print axioms MazurTransfer.Order13CubicActualInfinityValuations.cubicPlusFunction_ord_at_negative

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the infinity-defined cubic functions with literal
ordinary-coordinate functions on the actual rational curve. Named downstream
consumer: the complete cusp principal divisor.
-/

noncomputable section
namespace MazurTransfer.Order13CubicActualOrdinaryChart
open AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13CubicNormChartCertificate
open Order13CubicActualInfinityValuations
local instance cubicActualOrdinaryOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem ordinaryMinus_image :
    algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ) (ordinaryMinus ℚ) =
      yImage ℚ - cubic (xImage ℚ) := by
  simp only [ordinaryMinus, cubic, map_sub, map_add, map_mul, map_pow, map_ofNat, map_one]
  rfl

theorem ordinaryPlus_image :
    algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ) (Order13CubicNormChartCertificate.ordinaryPlus ℚ) =
      yImage ℚ + cubic (xImage ℚ) := by
  simp only [Order13CubicNormChartCertificate.ordinaryPlus, cubic, map_add, map_mul, map_pow, map_ofNat, map_one]
  rfl

theorem normMinus_image : normMinus = wImage ℚ - reciprocalCubic (zImage ℚ) := by
  simp only [normMinus, reciprocalMinus, reciprocalCubic, map_sub, map_add, map_mul, map_pow, map_ofNat, map_one]
  rfl

theorem normPlus_image : normPlus = wImage ℚ + reciprocalCubic (zImage ℚ) := by
  simp only [normPlus, reciprocalPlus, reciprocalCubic, map_add, map_mul, map_pow, map_ofNat, map_one]
  rfl

theorem ordinaryMinus_mul_zImage :
    algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ) (ordinaryMinus ℚ) * zImage ℚ ^ 3 = normMinus := by
  rw [ordinaryMinus_image, normMinus_image, yImage_overlap, xImage_eq_inverse]
  unfold cubic reciprocalCubic
  field_simp [zImage_ne_zero ℚ]
  <;> ring

theorem ordinaryPlus_mul_zImage :
    algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ) (Order13CubicNormChartCertificate.ordinaryPlus ℚ) * zImage ℚ ^ 3 = normPlus := by
  rw [ordinaryPlus_image, normPlus_image, yImage_overlap, xImage_eq_inverse]
  unfold cubic reciprocalCubic
  field_simp [zImage_ne_zero ℚ]
  <;> ring

theorem cubicMinusFunction_eq_ordinaryMinus : cubicMinusFunction =
    algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ) (ordinaryMinus ℚ) := by
  apply (div_eq_iff (pow_ne_zero 3 zField_ne_zero)).mpr
  exact ordinaryMinus_mul_zImage.symm

theorem cubicPlusFunction_eq_ordinaryPlus : cubicPlusFunction =
    algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ) (Order13CubicNormChartCertificate.ordinaryPlus ℚ) := by
  apply (div_eq_iff (pow_ne_zero 3 zField_ne_zero)).mpr
  exact ordinaryPlus_mul_zImage.symm

theorem cubicMinusFunction_eq : cubicMinusFunction = yImage ℚ - cubic (xImage ℚ) :=
  cubicMinusFunction_eq_ordinaryMinus.trans ordinaryMinus_image

theorem cubicPlusFunction_eq : cubicPlusFunction = yImage ℚ + cubic (xImage ℚ) :=
  cubicPlusFunction_eq_ordinaryPlus.trans ordinaryPlus_image

theorem cubicMinusFunction_ne_zero : cubicMinusFunction ≠ 0 :=
  div_ne_zero normMinus_ne_zero (pow_ne_zero 3 zField_ne_zero)

theorem cubicPlusFunction_ne_zero : cubicPlusFunction ≠ 0 :=
  div_ne_zero normPlus_ne_zero (pow_ne_zero 3 zField_ne_zero)

end MazurTransfer.Order13CubicActualOrdinaryChart
#print axioms MazurTransfer.Order13CubicActualOrdinaryChart.cubicMinusFunction_eq
#print axioms MazurTransfer.Order13CubicActualOrdinaryChart.cubicPlusFunction_eq


