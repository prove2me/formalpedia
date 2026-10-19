-- Prove2me | Definitions.Def_MazurTransfer_Order13CubicDiamondOrbitOriginalDataAndCertificates20261018
-- name    : MazurTransfer_Order13CubicDiamondOrbitOriginalDataAndCertificates20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T19:24:52.294017+00:00
-- url     : https://prove2.me/theorems/829eadbe-185d-4296-a1b6-b24b8d28c989
-- title:
--   Original cubic diamond transforms and infinity-place orbit certificates
-- statement:
--   Retain the original first and second cubic diamond transforms, their local infinity-order certificates, and transport to the diamond orbit of the actual infinity places. All seventy-two complete original declaration types and twenty-one whole nonproof values are compared, together with five complete context-provider types and the generic scalar-algebra provider value over every original characteristic-zero field. Named downstream consumers are cubic place-order characterization and the infinity-class eigenvalue.
-- source:
--   Retained original MazurTheorem cubic and diamond-orbit modules, Apache-2.0, Vas and contributors. Complete original declaration types and whole nonproof constructor values are compared. These interfaces package original data and proved certificates; they add no arithmetic assumption or new owned theorem-acceptance credit.

import Mathlib
import Definitions.Def_MazurTransfer_Order13CubicNormChartOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13CubicInfinityLocalOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13CubicActualFunctionFieldOriginalDataAndCertificatesSinglePublicUniformizerContextV320261018
import Definitions.Def_MazurTransfer_Order13FieldDiamondFunctionFieldAutomorphismData
import Theorems.Thm_MazurTransfer_order13_cubic_diamond_transform_identities
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original first and second diamond transforms of the cubic functions, their local infinity orders, and transport to the diamond orbit of the actual infinity places. Named downstream consumers: Order13CubicPlaceOrderCharacterization and Order13CubicHyperellipticPlaceAction, used in the infinity-class eigenvalue. Original data, field hypotheses and exact valuation certificates are retained.
-/
universe u
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: reciprocal chart numerators of the first two diamond
transforms of y-g(x). Named downstream consumer: cusp vanishing orders.
-/

noncomputable section
namespace MazurTransfer.Order13CubicDiamondChartCertificate
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13PellChartCertificate
variable {R : Type u} [CommRing R]

def firstCubic (z : R) : R := 1 + z - z ^ 3
def secondCubic (z : R) : R := 1 + 3 * z + 2 * z ^ 2 + z ^ 3

theorem first_norm_identity (z : R) :
    infinitySextic z - firstCubic z ^ 2 = 4 * z ^ 3 * (1 + z) ^ 2 := by
  simp only [infinitySextic, firstCubic]
  ring

theorem second_norm_identity (z : R) :
    infinitySextic z - secondCubic z ^ 2 = -4 * z * (1 + z) ^ 3 := by
  simp only [infinitySextic, secondCubic]
  ring

def firstMinus (R : Type u) [CommRing R] : ReciprocalRing R :=
  wCoordinate R - firstCubic (zCoordinate R)
def firstPlus (R : Type u) [CommRing R] : ReciprocalRing R :=
  wCoordinate R + firstCubic (zCoordinate R)
def secondMinus (R : Type u) [CommRing R] : ReciprocalRing R :=
  wCoordinate R - secondCubic (zCoordinate R)
def secondPlus (R : Type u) [CommRing R] : ReciprocalRing R :=
  wCoordinate R + secondCubic (zCoordinate R)

theorem first_product (R : Type u) [CommRing R] :
    firstMinus R * firstPlus R = 4 * zCoordinate R ^ 3 * (1 + zCoordinate R) ^ 2 := by
  have hw := wCoordinate_sq R
  have hw' : wCoordinate R ^ 2 = infinitySextic (zCoordinate R) := by
    simpa only [reciprocalPolynomial, infinitySextic, map_add, map_mul, map_pow,
      _root_.map_ofNat, _root_.map_one, Polynomial.aeval_X, add_comm, add_left_comm, add_assoc] using hw
  calc
    _ = wCoordinate R ^ 2 - firstCubic (zCoordinate R) ^ 2 := by dsimp [firstMinus, firstPlus]; ring
    _ = _ := by rw [hw']; exact first_norm_identity _

theorem second_product (R : Type u) [CommRing R] :
    secondMinus R * secondPlus R = -4 * zCoordinate R * (1 + zCoordinate R) ^ 3 := by
  have hw := wCoordinate_sq R
  have hw' : wCoordinate R ^ 2 = infinitySextic (zCoordinate R) := by
    simpa only [reciprocalPolynomial, infinitySextic, map_add, map_mul, map_pow,
      _root_.map_ofNat, _root_.map_one, Polynomial.aeval_X, add_comm, add_left_comm, add_assoc] using hw
  calc
    _ = wCoordinate R ^ 2 - secondCubic (zCoordinate R) ^ 2 := by dsimp [secondMinus, secondPlus]; ring
    _ = _ := by rw [hw']; exact second_norm_identity _

theorem firstMinus_evaluation (R : Type u) [CommRing R] (a : R) (ha : a ^ 2 = 1) :
    Order13InfinityEvaluationKernel.evaluation R a ha (firstMinus R) = a - 1 := by
  simp [firstMinus, firstCubic, Order13InfinityEvaluationKernel.evaluation,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_z,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_w]
theorem firstPlus_evaluation (R : Type u) [CommRing R] (a : R) (ha : a ^ 2 = 1) :
    Order13InfinityEvaluationKernel.evaluation R a ha (firstPlus R) = a + 1 := by
  simp [firstPlus, firstCubic, Order13InfinityEvaluationKernel.evaluation,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_z,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_w]
theorem secondMinus_evaluation (R : Type u) [CommRing R] (a : R) (ha : a ^ 2 = 1) :
    Order13InfinityEvaluationKernel.evaluation R a ha (secondMinus R) = a - 1 := by
  simp [secondMinus, secondCubic, Order13InfinityEvaluationKernel.evaluation,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_z,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_w]
theorem secondPlus_evaluation (R : Type u) [CommRing R] (a : R) (ha : a ^ 2 = 1) :
    Order13InfinityEvaluationKernel.evaluation R a ha (secondPlus R) = a + 1 := by
  simp [secondPlus, secondCubic, Order13InfinityEvaluationKernel.evaluation,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_z,
    MazurTransfer.PellInfinityEvaluationHelpers20261017.reciprocalInfinityEvaluation_w]

end MazurTransfer.Order13CubicDiamondChartCertificate
#print axioms MazurTransfer.Order13CubicDiamondChartCertificate.first_product
#print axioms MazurTransfer.Order13CubicDiamondChartCertificate.second_product

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the diamond-transformed reciprocal numerators have orders
three and one at the appropriate infinity branches. Named downstream
consumer: actual cusp valuations of the original cubic function.
-/

noncomputable section
namespace MazurTransfer.Order13CubicDiamondInfinityLocalOrders
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13InfinityLocalParameter Order13CubicDiamondChartCertificate
variable (K : Type u) [Field K]
abbrev positiveProof := Order13PellInfinityLocalOrders.positiveProof K
abbrev negativeProof := Order13PellInfinityLocalOrders.negativeProof K

def firstMinus (a : K) (ha : a ^ 2 = 1) : LocalRing K a ha :=
  algebraMap (ReciprocalRing K) (LocalRing K a ha) (Order13CubicDiamondChartCertificate.firstMinus K)

def firstPlus (a : K) (ha : a ^ 2 = 1) : LocalRing K a ha :=
  algebraMap (ReciprocalRing K) (LocalRing K a ha) (Order13CubicDiamondChartCertificate.firstPlus K)

theorem first_product (a : K) (ha : a ^ 2 = 1) :
    firstMinus K a ha * firstPlus K a ha = 4 * z K a ha ^ 3 * (1 + z K a ha) ^ 2 := by
  have h := congrArg (algebraMap (ReciprocalRing K) (LocalRing K a ha)) (Order13CubicDiamondChartCertificate.first_product K)
  simpa only [firstMinus, firstPlus, z, map_mul, map_neg, _root_.map_ofNat, map_pow, map_add, map_one, pow_one] using h

theorem firstPlus_isUnit_at_positive (h2 : (2 : K) ≠ 0) :
    IsUnit (firstPlus K 1 (positiveProof K)) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K 1 (positiveProof K))
    (infinityIdeal K 1 (positiveProof K)) _).mpr
  change Order13InfinityEvaluationKernel.evaluation K 1 (positiveProof K) (Order13CubicDiamondChartCertificate.firstPlus K) ≠ 0
  rw [Order13CubicDiamondChartCertificate.firstPlus_evaluation]
  simpa only [one_add_one_eq_two] using h2

theorem firstMinus_isUnit_at_negative (h2 : (2 : K) ≠ 0) :
    IsUnit (firstMinus K (-1) (negativeProof K)) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K (-1) (negativeProof K))
    (infinityIdeal K (-1) (negativeProof K)) _).mpr
  change Order13InfinityEvaluationKernel.evaluation K (-1) (negativeProof K) (Order13CubicDiamondChartCertificate.firstMinus K) ≠ 0
  rw [Order13CubicDiamondChartCertificate.firstMinus_evaluation]
  have heq : (-1 : K) - 1 = -(2 : K) := by ring
  rw [heq]
  exact neg_ne_zero.mpr h2

theorem first_unitFactor (a : K) (ha : a ^ 2 = 1) (h2 : (2 : K) ≠ 0) :
    IsUnit (4 * (1 + z K a ha) ^ 2) := by
  have h4 := Order13PellInfinityLocalOrders.neg_four_isUnit K a ha h2
  have h4p : IsUnit (4 : LocalRing K a ha) := by simpa using h4.neg
  exact h4p.mul ((Order13CubicInfinityLocalOrders.one_add_z_isUnit K a ha).pow 2)

theorem firstMinus_at_positive_associated (h2 : (2 : K) ≠ 0) :
    Associated (firstMinus K 1 (positiveProof K)) (z K 1 (positiveProof K) ^ 3) := by
  apply (associated_mul_isUnit_left_iff (firstPlus_isUnit_at_positive K h2)).mp
  rw [first_product]
  have heq : 4 * z K 1 (positiveProof K) ^ 3 * (1 + z K 1 (positiveProof K)) ^ 2 =
      (4 * (1 + z K 1 (positiveProof K)) ^ 2) * z K 1 (positiveProof K) ^ 3 := by ring
  rw [heq]
  exact associated_unit_mul_left _ _ (first_unitFactor K 1 (positiveProof K) h2)

theorem firstPlus_at_negative_associated (h2 : (2 : K) ≠ 0) :
    Associated (firstPlus K (-1) (negativeProof K)) (z K (-1) (negativeProof K) ^ 3) := by
  apply (associated_isUnit_mul_left_iff (firstMinus_isUnit_at_negative K h2)).mp
  rw [first_product]
  have heq : 4 * z K (-1) (negativeProof K) ^ 3 * (1 + z K (-1) (negativeProof K)) ^ 2 =
      (4 * (1 + z K (-1) (negativeProof K)) ^ 2) * z K (-1) (negativeProof K) ^ 3 := by ring
  rw [heq]
  exact associated_unit_mul_left _ _ (first_unitFactor K (-1) (negativeProof K) h2)

def secondMinus (a : K) (ha : a ^ 2 = 1) : LocalRing K a ha :=
  algebraMap (ReciprocalRing K) (LocalRing K a ha) (Order13CubicDiamondChartCertificate.secondMinus K)

def secondPlus (a : K) (ha : a ^ 2 = 1) : LocalRing K a ha :=
  algebraMap (ReciprocalRing K) (LocalRing K a ha) (Order13CubicDiamondChartCertificate.secondPlus K)

theorem second_product (a : K) (ha : a ^ 2 = 1) :
    secondMinus K a ha * secondPlus K a ha = -4 * z K a ha ^ 1 * (1 + z K a ha) ^ 3 := by
  have h := congrArg (algebraMap (ReciprocalRing K) (LocalRing K a ha)) (Order13CubicDiamondChartCertificate.second_product K)
  simpa only [secondMinus, secondPlus, z, map_mul, map_neg, _root_.map_ofNat, map_pow, map_add, map_one, pow_one] using h

theorem secondPlus_isUnit_at_positive (h2 : (2 : K) ≠ 0) :
    IsUnit (secondPlus K 1 (positiveProof K)) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K 1 (positiveProof K))
    (infinityIdeal K 1 (positiveProof K)) _).mpr
  change Order13InfinityEvaluationKernel.evaluation K 1 (positiveProof K) (Order13CubicDiamondChartCertificate.secondPlus K) ≠ 0
  rw [Order13CubicDiamondChartCertificate.secondPlus_evaluation]
  simpa only [one_add_one_eq_two] using h2

theorem secondMinus_isUnit_at_negative (h2 : (2 : K) ≠ 0) :
    IsUnit (secondMinus K (-1) (negativeProof K)) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K (-1) (negativeProof K))
    (infinityIdeal K (-1) (negativeProof K)) _).mpr
  change Order13InfinityEvaluationKernel.evaluation K (-1) (negativeProof K) (Order13CubicDiamondChartCertificate.secondMinus K) ≠ 0
  rw [Order13CubicDiamondChartCertificate.secondMinus_evaluation]
  have heq : (-1 : K) - 1 = -(2 : K) := by ring
  rw [heq]
  exact neg_ne_zero.mpr h2

theorem second_unitFactor (a : K) (ha : a ^ 2 = 1) (h2 : (2 : K) ≠ 0) :
    IsUnit (-4 * (1 + z K a ha) ^ 3) := by
  have h4 := Order13PellInfinityLocalOrders.neg_four_isUnit K a ha h2
  exact h4.mul ((Order13CubicInfinityLocalOrders.one_add_z_isUnit K a ha).pow 3)

theorem secondMinus_at_positive_associated (h2 : (2 : K) ≠ 0) :
    Associated (secondMinus K 1 (positiveProof K)) (z K 1 (positiveProof K) ^ 1) := by
  apply (associated_mul_isUnit_left_iff (secondPlus_isUnit_at_positive K h2)).mp
  rw [second_product]
  have heq : -4 * z K 1 (positiveProof K) ^ 1 * (1 + z K 1 (positiveProof K)) ^ 3 =
      (-4 * (1 + z K 1 (positiveProof K)) ^ 3) * z K 1 (positiveProof K) ^ 1 := by ring
  rw [heq]
  exact associated_unit_mul_left _ _ (second_unitFactor K 1 (positiveProof K) h2)

theorem secondPlus_at_negative_associated (h2 : (2 : K) ≠ 0) :
    Associated (secondPlus K (-1) (negativeProof K)) (z K (-1) (negativeProof K) ^ 1) := by
  apply (associated_isUnit_mul_left_iff (secondMinus_isUnit_at_negative K h2)).mp
  rw [second_product]
  have heq : -4 * z K (-1) (negativeProof K) ^ 1 * (1 + z K (-1) (negativeProof K)) ^ 3 =
      (-4 * (1 + z K (-1) (negativeProof K)) ^ 3) * z K (-1) (negativeProof K) ^ 1 := by ring
  rw [heq]
  exact associated_unit_mul_left _ _ (second_unitFactor K (-1) (negativeProof K) h2)

end MazurTransfer.Order13CubicDiamondInfinityLocalOrders
#print axioms MazurTransfer.Order13CubicDiamondInfinityLocalOrders.firstMinus_at_positive_associated
#print axioms MazurTransfer.Order13CubicDiamondInfinityLocalOrders.secondPlus_at_negative_associated

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the reciprocal expressions of the two cubic diamond
transforms have infinity orders (3,0) and (0,1). Named downstream consumer:
cusp valuations after transporting by the actual function-field diamond.
-/

noncomputable section
namespace MazurTransfer.Order13CubicDiamondActualInfinityValuations
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter Order13ReciprocalChartActualFunctionField
open Order13PellActualInfinityValuations
open Order13CubicActualInfinityValuations (zField)
local instance order13CubicDiamondActualInfinityValuationsOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
abbrev positiveProof := Order13CubicDiamondInfinityLocalOrders.positiveProof ℚ
abbrev negativeProof := Order13CubicDiamondInfinityLocalOrders.negativeProof ℚ

abbrev firstNumerator : actualCurveFunctionField ℚ :=
  algebraMap (ReciprocalRing ℚ) (actualCurveFunctionField ℚ) (Order13CubicDiamondChartCertificate.firstMinus ℚ)
abbrev secondNumerator : actualCurveFunctionField ℚ :=
  algebraMap (ReciprocalRing ℚ) (actualCurveFunctionField ℚ) (Order13CubicDiamondChartCertificate.secondPlus ℚ)
def firstTransform : actualCurveFunctionField ℚ := firstNumerator / (1 + zField) ^ 3
def secondTransform : actualCurveFunctionField ℚ := secondNumerator

theorem firstNumerator_ord_at_positive :
    (infinityPlace 1 positiveProof).ord firstNumerator = 3 := by
  rw [firstNumerator, ← localEmbedding_coordinate ℚ 1 positiveProof]
  exact infinityPlace_ord_associated_zpow _ _ _ 3
    (Order13CubicDiamondInfinityLocalOrders.firstMinus_at_positive_associated ℚ (by norm_num))

theorem firstNumerator_ord_at_negative :
    (infinityPlace (-1) negativeProof).ord firstNumerator = 0 := by
  rw [firstNumerator, ← localEmbedding_coordinate ℚ (-1) negativeProof]
  exact infinityPlace_ord_isUnit _ _ _
    (Order13CubicDiamondInfinityLocalOrders.firstMinus_isUnit_at_negative ℚ (by norm_num))

theorem secondNumerator_ord_at_positive :
    (infinityPlace 1 positiveProof).ord secondNumerator = 0 := by
  rw [secondNumerator, ← localEmbedding_coordinate ℚ 1 positiveProof]
  exact infinityPlace_ord_isUnit _ _ _
    (Order13CubicDiamondInfinityLocalOrders.secondPlus_isUnit_at_positive ℚ (by norm_num))

theorem secondNumerator_ord_at_negative :
    (infinityPlace (-1) negativeProof).ord secondNumerator = 1 := by
  rw [secondNumerator, ← localEmbedding_coordinate ℚ (-1) negativeProof]
  exact infinityPlace_ord_associated_zpow _ _ _ 1
    (Order13CubicDiamondInfinityLocalOrders.secondPlus_at_negative_associated ℚ (by norm_num))

theorem firstNumerator_ne_zero : firstNumerator ≠ 0 := by
  rw [firstNumerator, ← localEmbedding_coordinate ℚ 1 positiveProof]
  apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
  exact (Order13CubicDiamondInfinityLocalOrders.firstMinus_at_positive_associated ℚ (by norm_num)).ne_zero_iff.mpr
    (pow_ne_zero 3 (Order13InfinityDiscreteValuationRing.z_ne_zero ℚ 1 positiveProof))

theorem secondNumerator_ne_zero : secondNumerator ≠ 0 := by
  rw [secondNumerator, ← localEmbedding_coordinate ℚ (-1) negativeProof]
  apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
  exact (Order13CubicDiamondInfinityLocalOrders.secondPlus_at_negative_associated ℚ (by norm_num)).ne_zero_iff.mpr
    (pow_ne_zero 1 (Order13InfinityDiscreteValuationRing.z_ne_zero ℚ (-1) negativeProof))

theorem one_add_zField_ord (a : ℚ) (ha : a ^ 2 = 1) :
    (infinityPlace a ha).ord (1 + zField) = 0 := by
  have heq : (1 + zField) = algebraMap (ReciprocalRing ℚ) (actualCurveFunctionField ℚ) (1 + zCoordinate ℚ) := by
    simp only [map_add, map_one, zField]
  rw [heq, ← localEmbedding_coordinate ℚ a ha]
  apply infinityPlace_ord_isUnit
  simpa only [map_add, map_one, z] using Order13CubicInfinityLocalOrders.one_add_z_isUnit ℚ a ha

theorem one_add_zField_ne_zero : 1 + zField ≠ 0 := by
  have heq : (1 + zField) = localEmbedding ℚ 1 positiveProof
      (1 + z ℚ 1 positiveProof) := by
    have h := localEmbedding_coordinate ℚ 1 positiveProof (1 + zCoordinate ℚ)
    simpa only [map_add, map_one, z, zField] using h.symm
  rw [heq]
  exact ((Order13CubicInfinityLocalOrders.one_add_z_isUnit ℚ 1 positiveProof).map
    (localEmbedding ℚ 1 positiveProof)).ne_zero

theorem firstTransform_ord (a : ℚ) (ha : a ^ 2 = 1) :
    (infinityPlace a ha).ord firstTransform = (infinityPlace a ha).ord firstNumerator := by
  rw [firstTransform, div_eq_mul_inv,
    Place.ord_mul _ firstNumerator_ne_zero (inv_ne_zero (pow_ne_zero 3 one_add_zField_ne_zero)),
    Place.ord_inv, ← zpow_natCast, Place.ord_zpow, one_add_zField_ord]
  simp

theorem firstTransform_ord_at_positive :
    (infinityPlace 1 positiveProof).ord firstTransform = 3 := by
  rw [firstTransform_ord, firstNumerator_ord_at_positive]

theorem firstTransform_ord_at_negative :
    (infinityPlace (-1) negativeProof).ord firstTransform = 0 := by
  rw [firstTransform_ord, firstNumerator_ord_at_negative]

theorem secondTransform_ord_at_positive :
    (infinityPlace 1 positiveProof).ord secondTransform = 0 := secondNumerator_ord_at_positive

theorem secondTransform_ord_at_negative :
    (infinityPlace (-1) negativeProof).ord secondTransform = 1 := secondNumerator_ord_at_negative

end MazurTransfer.Order13CubicDiamondActualInfinityValuations
#print axioms MazurTransfer.Order13CubicDiamondActualInfinityValuations.firstTransform_ord_at_positive
#print axioms MazurTransfer.Order13CubicDiamondActualInfinityValuations.secondTransform_ord_at_negative

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact accepted public coordinate identities compute
the first two diamond transforms of the actual cubic function. Named
 downstream consumer: actual diamond-orbit cusp valuations.
-/

noncomputable section
namespace MazurTransfer.Order13CubicDiamondPublicCompatibility
open AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart
open Order13CubicActualInfinityValuations
open Order13CubicActualOrdinaryChart
open Order13CubicDiamondActualInfinityValuations
open Order13FieldDiamondFunctionFieldMap
open Order13FieldDiamondFunctionFieldAutomorphism
open Order13DiamondSexticIterates Order13DiamondSexticSymmetry
open Order13FieldOrdinaryPolynomialTranscendence
local instance order13CubicDiamondPublicCompatibilityOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem first_field_expression : diamondFieldMap ℚ cubicMinusFunction =
    (yImage ℚ - xImage ℚ ^ 3 - xImage ℚ ^ 2 + 1) / (xImage ℚ + 1) ^ 3 := by
  rw [cubicMinusFunction_eq]
  simp only [Order13CubicNormChartCertificate.cubic, map_sub, map_add, map_mul, map_pow, map_ofNat, map_one,
    diamondFieldMap_x, diamondFieldMap_y, diamondX, diamondY]
  exact (MazurTransfer.order13_cubic_diamond_transform_identities (actualCurveFunctionField ℚ)
    (xImage ℚ) (yImage ℚ) (xImage_ne_zero ℚ) (xImage_add_one_ne_zero ℚ)).1

theorem second_field_expression : diamondSecond ℚ cubicMinusFunction =
    (yImage ℚ + xImage ℚ ^ 3 + 3 * xImage ℚ ^ 2 + 2 * xImage ℚ + 1) / xImage ℚ ^ 3 := by
  rw [cubicMinusFunction_eq]
  simp only [diamondSecond, RingHom.comp_apply, Order13CubicNormChartCertificate.cubic,
    map_sub, map_add, map_mul, map_pow, map_ofNat, map_one, diamondFieldMap_x, diamondFieldMap_y,
    map_diamondX, map_diamondY]
  rw [diamondX_sq _ (xImage_ne_zero ℚ) (xImage_add_one_ne_zero ℚ),
    diamondY_sq _ _ (xImage_ne_zero ℚ) (xImage_add_one_ne_zero ℚ)]
  exact (MazurTransfer.order13_cubic_diamond_transform_identities (actualCurveFunctionField ℚ)
    (xImage ℚ) (yImage ℚ) (xImage_ne_zero ℚ) (xImage_add_one_ne_zero ℚ)).2

theorem firstNumerator_image : firstNumerator =
    wImage ℚ - (1 + zImage ℚ - zImage ℚ ^ 3) := by
  simp only [firstNumerator, Order13CubicDiamondChartCertificate.firstMinus,
    Order13CubicDiamondChartCertificate.firstCubic, map_sub, map_add, map_pow, map_one]
  rfl

theorem secondNumerator_image : secondNumerator =
    wImage ℚ + (1 + 3 * zImage ℚ + 2 * zImage ℚ ^ 2 + zImage ℚ ^ 3) := by
  simp only [secondNumerator, Order13CubicDiamondChartCertificate.secondPlus,
    Order13CubicDiamondChartCertificate.secondCubic, map_add, map_mul, map_pow, map_one, map_ofNat]
  rfl

theorem first_diamond_transform : diamondAlgEquiv ℚ cubicMinusFunction = firstTransform := by
  change diamondFieldMap ℚ cubicMinusFunction = firstTransform
  rw [first_field_expression, firstTransform]
  apply (div_eq_div_iff (pow_ne_zero 3 (xImage_add_one_ne_zero ℚ))
    (pow_ne_zero 3 one_add_zField_ne_zero)).mpr
  rw [firstNumerator_image, yImage_overlap, xImage_eq_inverse]
  change _ * (1 + zImage ℚ) ^ 3 = _
  field_simp [zImage_ne_zero ℚ]
  <;> ring

theorem second_diamond_transform : (diamondAlgEquiv ℚ * diamondAlgEquiv ℚ) cubicMinusFunction = secondTransform := by
  change diamondSecond ℚ cubicMinusFunction = secondTransform
  rw [second_field_expression]
  change _ = secondNumerator
  apply (div_eq_iff (pow_ne_zero 3 (xImage_ne_zero ℚ))).mpr
  rw [secondNumerator_image, yImage_overlap, xImage_eq_inverse]
  field_simp [zImage_ne_zero ℚ]
  <;> ring

end MazurTransfer.Order13CubicDiamondPublicCompatibility
#print axioms MazurTransfer.Order13CubicDiamondPublicCompatibility.first_diamond_transform
#print axioms MazurTransfer.Order13CubicDiamondPublicCompatibility.second_diamond_transform

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transport literal cubic valuations to the actual diamond
orbit of the infinity places. Named downstream consumer: full cusp
principal divisor and infinity-class norm identification.
-/

noncomputable section
namespace MazurTransfer.Order13CubicDiamondOrbitValuations
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualInfinityValuations
open Order13CubicActualInfinityValuations
open Order13CubicDiamondActualInfinityValuations
open Order13FieldDiamondFunctionFieldAutomorphism
open Order13CubicDiamondPublicCompatibility
local instance order13CubicDiamondOrbitValuationsOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

abbrev diamond := diamondAlgEquiv ℚ
abbrev positiveInfinity := infinityPlace 1 positiveProof
abbrev negativeInfinity := infinityPlace (-1) negativeProof

def firstPositivePlace : Place ℚ (actualCurveFunctionField ℚ) := diamond⁻¹ • positiveInfinity
def firstNegativePlace : Place ℚ (actualCurveFunctionField ℚ) := diamond⁻¹ • negativeInfinity
def secondPositivePlace : Place ℚ (actualCurveFunctionField ℚ) := (diamond * diamond)⁻¹ • positiveInfinity
def secondNegativePlace : Place ℚ (actualCurveFunctionField ℚ) := (diamond * diamond)⁻¹ • negativeInfinity

theorem ord_inverse_smul (σ : actualCurveFunctionField ℚ ≃ₐ[ℚ] actualCurveFunctionField ℚ)
    (v : Place ℚ (actualCurveFunctionField ℚ)) (f : actualCurveFunctionField ℚ) :
    (σ⁻¹ • v).ord f = v.ord (σ f) := by
  have h := Place.ord_smul σ (σ⁻¹ • v) f
  simpa only [smul_inv_smul] using h.symm

theorem cubicMinusFunction_ord_firstPositive : firstPositivePlace.ord cubicMinusFunction = 3 := by
  rw [firstPositivePlace, ord_inverse_smul, first_diamond_transform]
  exact firstTransform_ord_at_positive

theorem cubicMinusFunction_ord_firstNegative : firstNegativePlace.ord cubicMinusFunction = 0 := by
  rw [firstNegativePlace, ord_inverse_smul, first_diamond_transform]
  exact firstTransform_ord_at_negative

theorem cubicMinusFunction_ord_secondPositive : secondPositivePlace.ord cubicMinusFunction = 0 := by
  rw [secondPositivePlace, ord_inverse_smul, second_diamond_transform]
  exact secondTransform_ord_at_positive

theorem cubicMinusFunction_ord_secondNegative : secondNegativePlace.ord cubicMinusFunction = 1 := by
  rw [secondNegativePlace, ord_inverse_smul, second_diamond_transform]
  exact secondTransform_ord_at_negative

theorem firstPositivePlace_ne_secondNegativePlace : firstPositivePlace ≠ secondNegativePlace := by
  intro h
  have h3 := cubicMinusFunction_ord_firstPositive
  rw [h, cubicMinusFunction_ord_secondNegative] at h3
  norm_num at h3

theorem firstPositivePlace_ne_infinity (a : ℚ) (ha : a ^ 2 = 1) (h : a = 1 ∨ a = -1) :
    firstPositivePlace ≠ infinityPlace a ha := by
  intro heq
  have h3 := cubicMinusFunction_ord_firstPositive
  rw [heq] at h3
  rcases h with rfl | rfl
  · rw [cubicMinusFunction_ord_at_positive] at h3
    norm_num at h3
  · rw [cubicMinusFunction_ord_at_negative] at h3
    norm_num at h3

theorem secondNegativePlace_ne_infinity (a : ℚ) (ha : a ^ 2 = 1) (h : a = 1 ∨ a = -1) :
    secondNegativePlace ≠ infinityPlace a ha := by
  intro heq
  have h1 := cubicMinusFunction_ord_secondNegative
  rw [heq] at h1
  rcases h with rfl | rfl
  · rw [cubicMinusFunction_ord_at_positive] at h1
    norm_num at h1
  · rw [cubicMinusFunction_ord_at_negative] at h1
    norm_num at h1

end MazurTransfer.Order13CubicDiamondOrbitValuations
#print axioms MazurTransfer.Order13CubicDiamondOrbitValuations.cubicMinusFunction_ord_firstPositive
#print axioms MazurTransfer.Order13CubicDiamondOrbitValuations.cubicMinusFunction_ord_secondNegative
#print axioms MazurTransfer.Order13CubicDiamondOrbitValuations.firstPositivePlace_ne_secondNegativePlace


