-- Prove2me | Definitions.Def_MazurTransfer_Order13CubicCuspLocalOriginalDataAndCertificates20261018
-- name    : MazurTransfer_Order13CubicCuspLocalOriginalDataAndCertificates20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T19:05:35.154261+00:00
-- url     : https://prove2.me/theorems/4fbe7a6a-5059-44af-af09-35a439551c24
-- title:
--   Original local cubic functions and cusp-order certificates
-- statement:
--   Retain the two original ordinary local cubic function constructors and their exact product, unit and associated-power certificates at the four ordinary cusps, including compatibility with the accepted discrete-valuation norm-factorization theorem. All twenty-eight complete original types and both nonproof values are compared, together with the two original rational nonzero-tangent fact-provider types. Named downstream consumer is the actual cubic cusp valuation calculation.
-- source:
--   Original retained MazurTheorem cubic and local-ring modules, Apache-2.0, Vas and contributors. Complete original declaration types and whole nonproof constructor values are compared. This packages existing checked constructors and their proved certificates; it adds no arithmetic assumption or new theorem acceptance credit.

import Mathlib
import Definitions.Def_MazurTransfer_Order13OrdinaryLocalOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13CubicNormChartOriginalDataAndCertificates20261018
import Theorems.Thm_MazurTransfer_dvr_norm_factorization_order
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original local cubic function constructors, associated powers of the ordinary cusp parameters, and exact factorization-order compatibility. Named downstream consumer: Order13CubicActualCuspValuations, used in the original cubic principal divisor and infinity-class eigenvalue. Original fields and characteristic hypotheses are retained.
-/
universe u
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal cubic functions are associated to the third
or first power of x-t at the four ordinary cusps. Named downstream
consumer: actual cusp place orders and the complete principal divisor.
-/

noncomputable section
namespace MazurTransfer.Order13CubicCuspLocalOrders
open MazurTorsion.XOneThirteenAffineCurve
open Order13OrdinaryLocalParameter Order13IntegralSections
open Order13CubicNormChartCertificate
variable (K : Type u) [Field K]

theorem zeroPositiveProof : (1 : K) ^ 2 = (sexticPolynomial K).eval 0 := by rw [sextic_eval_zero]; simp
theorem zeroNegativeProof : (-1 : K) ^ 2 = (sexticPolynomial K).eval 0 := by rw [sextic_eval_zero]; simp
theorem negOnePositiveProof : (1 : K) ^ 2 = (sexticPolynomial K).eval (-1) := by rw [sextic_eval_neg_one]; simp
theorem negOneNegativeProof : (-1 : K) ^ 2 = (sexticPolynomial K).eval (-1) := by rw [sextic_eval_neg_one]; simp

def minus (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) : LocalRing K t a ha :=
  algebraMap (CoordinateRing K) (LocalRing K t a ha) (ordinaryMinus K)
def plus (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) : LocalRing K t a ha :=
  algebraMap (CoordinateRing K) (LocalRing K t a ha) (ordinaryPlus K)

theorem product (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) :
    minus K t a ha * plus K t a ha = -4 * x K t a ha ^ 3 * (x K t a ha + 1) := by
  have h := congrArg (algebraMap (CoordinateRing K) (LocalRing K t a ha)) (ordinary_product K)
  simpa only [minus, plus, x, map_mul, map_pow, map_neg, map_ofNat, map_add, map_one] using h

theorem minus_evaluation (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) :
    ordinaryEvaluation K t a ha (ordinaryMinus K) = a - cubic t := by
  simp only [ordinaryMinus, cubic, map_sub, map_add, map_mul, map_pow, _root_.map_ofNat, map_one, ordinaryEvaluation_x, ordinaryEvaluation_y]
theorem plus_evaluation (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) :
    ordinaryEvaluation K t a ha (ordinaryPlus K) = a + cubic t := by
  simp only [ordinaryPlus, cubic, map_add, map_mul, map_pow, _root_.map_ofNat, map_one, ordinaryEvaluation_x, ordinaryEvaluation_y]

theorem minus_isUnit (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) (h : a - cubic t ≠ 0) :
    IsUnit (minus K t a ha) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K t a ha) (pointIdeal K t a ha) _).mpr
  change ordinaryEvaluation K t a ha (ordinaryMinus K) ≠ 0
  rw [minus_evaluation]
  exact h

theorem plus_isUnit (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) (h : a + cubic t ≠ 0) :
    IsUnit (plus K t a ha) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K t a ha) (pointIdeal K t a ha) _).mpr
  change ordinaryEvaluation K t a ha (ordinaryPlus K) ≠ 0
  rw [plus_evaluation]
  exact h

variable [CharZero K]

theorem neg_four_isUnit (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) :
    IsUnit (-4 : LocalRing K t a ha) := by
  have h := (isUnit_iff_ne_zero.mpr (by norm_num : (-4 : K) ≠ 0)).map
    ((algebraMap (CoordinateRing K) (LocalRing K t a ha)).comp (algebraMap K (CoordinateRing K)))
  simpa only [RingHom.comp_apply, map_neg, map_ofNat] using h

theorem x_isUnit_at_neg_one (a : K) (ha : a ^ 2 = (sexticPolynomial K).eval (-1)) :
    IsUnit (x K (-1) a ha) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K (-1) a ha) (pointIdeal K (-1) a ha) _).mpr
  change ordinaryEvaluation K (-1) a ha (xCoordinate K) ≠ 0
  rw [ordinaryEvaluation_x]
  exact neg_ne_zero.mpr one_ne_zero

theorem x_add_one_isUnit_at_zero (a : K) (ha : a ^ 2 = (sexticPolynomial K).eval 0) :
    IsUnit (x K 0 a ha + 1) := by
  have h : IsUnit (algebraMap (CoordinateRing K) (LocalRing K 0 a ha) (xCoordinate K + 1)) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K 0 a ha) (pointIdeal K 0 a ha) _).mpr
    change ordinaryEvaluation K 0 a ha (xCoordinate K + 1) ≠ 0
    simp only [map_add, ordinaryEvaluation_x, map_one, zero_add, ne_eq, one_ne_zero, not_false_eq_true]
  simpa only [map_add, map_one, x] using h

omit [CharZero K] in
theorem parameter_at_zero (a : K) (ha : a ^ 2 = (sexticPolynomial K).eval 0) : parameter K 0 a ha = x K 0 a ha := by
  simp only [parameter, constant, map_zero, sub_zero]
omit [CharZero K] in
theorem parameter_at_neg_one (a : K) (ha : a ^ 2 = (sexticPolynomial K).eval (-1)) : parameter K (-1) a ha = x K (-1) a ha + 1 := by
  simp only [parameter, constant, map_neg, map_one, sub_neg_eq_add]

theorem plus_isUnit_at_zeroPositive : IsUnit (plus K 0 1 (zeroPositiveProof K)) := by
  apply plus_isUnit
  norm_num [cubic]

theorem minus_isUnit_at_zeroNegative : IsUnit (minus K 0 (-1) (zeroNegativeProof K)) := by
  apply minus_isUnit
  norm_num [cubic]

theorem minus_isUnit_at_negOnePositive : IsUnit (minus K (-1) 1 (negOnePositiveProof K)) := by
  apply minus_isUnit
  norm_num [cubic]

theorem plus_isUnit_at_negOneNegative : IsUnit (plus K (-1) (-1) (negOneNegativeProof K)) := by
  apply plus_isUnit
  norm_num [cubic]

theorem minus_at_zeroPositive_associated :
    Associated (minus K 0 1 (zeroPositiveProof K)) (parameter K 0 1 (zeroPositiveProof K) ^ 3) := by
  apply (associated_mul_isUnit_left_iff (plus_isUnit_at_zeroPositive K)).mp
  rw [product]
  rw [parameter_at_zero]
  have heq : -4 * x K 0 1 (zeroPositiveProof K) ^ 3 * (x K 0 1 (zeroPositiveProof K) + 1) =
      (-4 * (x K 0 1 (zeroPositiveProof K) + 1)) * x K 0 1 (zeroPositiveProof K) ^ 3 := by ring
  rw [heq]
  exact associated_unit_mul_left _ _ ((neg_four_isUnit K 0 1 (zeroPositiveProof K)).mul
    (x_add_one_isUnit_at_zero K 1 (zeroPositiveProof K)))

theorem plus_at_zeroNegative_associated :
    Associated (plus K 0 (-1) (zeroNegativeProof K)) (parameter K 0 (-1) (zeroNegativeProof K) ^ 3) := by
  apply (associated_isUnit_mul_left_iff (minus_isUnit_at_zeroNegative K)).mp
  rw [product]
  rw [parameter_at_zero]
  have heq : -4 * x K 0 (-1) (zeroNegativeProof K) ^ 3 * (x K 0 (-1) (zeroNegativeProof K) + 1) =
      (-4 * (x K 0 (-1) (zeroNegativeProof K) + 1)) * x K 0 (-1) (zeroNegativeProof K) ^ 3 := by ring
  rw [heq]
  exact associated_unit_mul_left _ _ ((neg_four_isUnit K 0 (-1) (zeroNegativeProof K)).mul
    (x_add_one_isUnit_at_zero K (-1) (zeroNegativeProof K)))

theorem plus_at_negOnePositive_associated :
    Associated (plus K (-1) 1 (negOnePositiveProof K)) (parameter K (-1) 1 (negOnePositiveProof K) ^ 1) := by
  apply (associated_isUnit_mul_left_iff (minus_isUnit_at_negOnePositive K)).mp
  rw [product]
  rw [pow_one, parameter_at_neg_one]
  exact associated_unit_mul_left _ _ ((neg_four_isUnit K (-1) 1 (negOnePositiveProof K)).mul
    ((x_isUnit_at_neg_one K 1 (negOnePositiveProof K)).pow 3))

theorem minus_at_negOneNegative_associated :
    Associated (minus K (-1) (-1) (negOneNegativeProof K)) (parameter K (-1) (-1) (negOneNegativeProof K) ^ 1) := by
  apply (associated_mul_isUnit_left_iff (plus_isUnit_at_negOneNegative K)).mp
  rw [product]
  rw [pow_one, parameter_at_neg_one]
  exact associated_unit_mul_left _ _ ((neg_four_isUnit K (-1) (-1) (negOneNegativeProof K)).mul
    ((x_isUnit_at_neg_one K (-1) (negOneNegativeProof K)).pow 3))

end MazurTransfer.Order13CubicCuspLocalOrders
#print axioms MazurTransfer.Order13CubicCuspLocalOrders.minus_at_zeroPositive_associated
#print axioms MazurTransfer.Order13CubicCuspLocalOrders.minus_at_negOneNegative_associated

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact accepted DVR order contract proves the four
cusp associations in the actual rational ordinary local rings. Named
 downstream consumer: actual finite cusp orders and cubic principal divisors.
-/

noncomputable section
namespace MazurTransfer.Order13CubicCuspPublicCompatibility
open Order13OrdinaryLocalParameter Order13CubicCuspLocalOrders
local instance : Fact (2 * (1 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Fact (2 * (-1 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem minus_at_zeroPositive_associated :
    Associated (minus ℚ 0 1 (zeroPositiveProof ℚ)) (parameter ℚ 0 1 (zeroPositiveProof ℚ) ^ 3) := by
  exact (MazurTransfer.dvr_norm_factorization_order (LocalRing ℚ 0 1 (zeroPositiveProof ℚ))
    (minus ℚ 0 1 (zeroPositiveProof ℚ)) (plus ℚ 0 1 (zeroPositiveProof ℚ))
    (-4 * (x ℚ 0 1 (zeroPositiveProof ℚ) + 1)) (parameter ℚ 0 1 (zeroPositiveProof ℚ)) 3
    (Order13OrdinaryDiscreteValuationRing.parameter_irreducible ℚ 0 1 (zeroPositiveProof ℚ))
    (plus_isUnit_at_zeroPositive ℚ) ((neg_four_isUnit ℚ 0 1 (zeroPositiveProof ℚ)).mul (x_add_one_isUnit_at_zero ℚ 1 (zeroPositiveProof ℚ))) (by
      rw [product, parameter_at_zero]
      ring)).1


theorem plus_at_zeroNegative_associated :
    Associated (plus ℚ 0 (-1) (zeroNegativeProof ℚ)) (parameter ℚ 0 (-1) (zeroNegativeProof ℚ) ^ 3) := by
  exact (MazurTransfer.dvr_norm_factorization_order (LocalRing ℚ 0 (-1) (zeroNegativeProof ℚ))
    (plus ℚ 0 (-1) (zeroNegativeProof ℚ)) (minus ℚ 0 (-1) (zeroNegativeProof ℚ))
    (-4 * (x ℚ 0 (-1) (zeroNegativeProof ℚ) + 1)) (parameter ℚ 0 (-1) (zeroNegativeProof ℚ)) 3
    (Order13OrdinaryDiscreteValuationRing.parameter_irreducible ℚ 0 (-1) (zeroNegativeProof ℚ))
    (minus_isUnit_at_zeroNegative ℚ) ((neg_four_isUnit ℚ 0 (-1) (zeroNegativeProof ℚ)).mul (x_add_one_isUnit_at_zero ℚ (-1) (zeroNegativeProof ℚ))) (by
      rw [mul_comm (plus ℚ 0 (-1) (zeroNegativeProof ℚ)) (minus ℚ 0 (-1) (zeroNegativeProof ℚ))]
      rw [product, parameter_at_zero]
      ring)).1


theorem plus_at_negOnePositive_associated :
    Associated (plus ℚ (-1) 1 (negOnePositiveProof ℚ)) (parameter ℚ (-1) 1 (negOnePositiveProof ℚ) ^ 1) := by
  exact (MazurTransfer.dvr_norm_factorization_order (LocalRing ℚ (-1) 1 (negOnePositiveProof ℚ))
    (plus ℚ (-1) 1 (negOnePositiveProof ℚ)) (minus ℚ (-1) 1 (negOnePositiveProof ℚ))
    (-4 * x ℚ (-1) 1 (negOnePositiveProof ℚ) ^ 3) (parameter ℚ (-1) 1 (negOnePositiveProof ℚ)) 1
    (Order13OrdinaryDiscreteValuationRing.parameter_irreducible ℚ (-1) 1 (negOnePositiveProof ℚ))
    (minus_isUnit_at_negOnePositive ℚ) ((neg_four_isUnit ℚ (-1) 1 (negOnePositiveProof ℚ)).mul ((x_isUnit_at_neg_one ℚ 1 (negOnePositiveProof ℚ)).pow 3)) (by
      rw [mul_comm (plus ℚ (-1) 1 (negOnePositiveProof ℚ)) (minus ℚ (-1) 1 (negOnePositiveProof ℚ))]
      rw [product, pow_one, parameter_at_neg_one])).1


theorem minus_at_negOneNegative_associated :
    Associated (minus ℚ (-1) (-1) (negOneNegativeProof ℚ)) (parameter ℚ (-1) (-1) (negOneNegativeProof ℚ) ^ 1) := by
  exact (MazurTransfer.dvr_norm_factorization_order (LocalRing ℚ (-1) (-1) (negOneNegativeProof ℚ))
    (minus ℚ (-1) (-1) (negOneNegativeProof ℚ)) (plus ℚ (-1) (-1) (negOneNegativeProof ℚ))
    (-4 * x ℚ (-1) (-1) (negOneNegativeProof ℚ) ^ 3) (parameter ℚ (-1) (-1) (negOneNegativeProof ℚ)) 1
    (Order13OrdinaryDiscreteValuationRing.parameter_irreducible ℚ (-1) (-1) (negOneNegativeProof ℚ))
    (plus_isUnit_at_negOneNegative ℚ) ((neg_four_isUnit ℚ (-1) (-1) (negOneNegativeProof ℚ)).mul ((x_isUnit_at_neg_one ℚ (-1) (negOneNegativeProof ℚ)).pow 3)) (by
      rw [product, pow_one, parameter_at_neg_one])).1


end MazurTransfer.Order13CubicCuspPublicCompatibility
#print axioms MazurTransfer.Order13CubicCuspPublicCompatibility.minus_at_zeroPositive_associated
#print axioms MazurTransfer.Order13CubicCuspPublicCompatibility.minus_at_negOneNegative_associated


