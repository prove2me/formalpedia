-- Prove2me | Definitions.Def_MazurTransfer_Order13CubicInfinityLocalOriginalDataAndCertificates20261018
-- name    : MazurTransfer_Order13CubicInfinityLocalOriginalDataAndCertificates20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T19:03:39.510683+00:00
-- url     : https://prove2.me/theorems/8782acc1-1001-4f52-a377-748cb0149c69
-- title:
--   Original local cubic functions and infinity orders
-- statement:
--   Retain the original two normalized cubic functions in the reciprocal-chart localizations, the two sign proofs, their product factorization, unit certificates, and associated-power certificates. All eleven complete original types and both nonproof constructor values are compared. Named downstream consumer is the actual cubic-function infinity valuation calculation.
-- source:
--   Original retained MazurTheorem cubic and local-ring modules, Apache-2.0, Vas and contributors. Complete original declaration types and whole nonproof constructor values are compared. This packages existing checked constructors and their proved certificates; it adds no arithmetic assumption or new theorem acceptance credit.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two normalized cubic numerators have orders zero
and two at the actual reciprocal-chart infinity localizations.
Named downstream consumer: the cubic principal divisor and its pole orders.
-/
import Definitions.Def_MazurTransfer_Order13CubicNormChartOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13PellInfinityLocalOrders

noncomputable section
universe u
namespace MazurTransfer.Order13CubicInfinityLocalOrders
open MazurTorsion.XOneThirteenProjectiveCurve Order13InfinityLocalParameter
open Order13CubicNormChartCertificate
variable (K : Type u) [Field K]

abbrev positiveProof := Order13PellInfinityLocalOrders.positiveProof K
abbrev negativeProof := Order13PellInfinityLocalOrders.negativeProof K

def minus (a : K) (ha : a ^ 2 = 1) : LocalRing K a ha :=
  algebraMap (ReciprocalRing K) (LocalRing K a ha) (reciprocalMinus K)
def plus (a : K) (ha : a ^ 2 = 1) : LocalRing K a ha :=
  algebraMap (ReciprocalRing K) (LocalRing K a ha) (reciprocalPlus K)

theorem product (a : K) (ha : a ^ 2 = 1) :
    minus K a ha * plus K a ha = -4 * z K a ha ^ 2 * (1 + z K a ha) := by
  have h := congrArg (algebraMap (ReciprocalRing K) (LocalRing K a ha)) (reciprocal_product K)
  simpa only [minus, plus, z, map_mul, map_neg, _root_.map_ofNat, map_pow, map_add, map_one] using h

theorem one_add_z_isUnit (a : K) (ha : a ^ 2 = 1) : IsUnit (1 + z K a ha) := by
  have h : IsUnit (algebraMap (ReciprocalRing K) (LocalRing K a ha) (1 + zCoordinate K)) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K a ha) (infinityIdeal K a ha) _).mpr
    change Order13InfinityEvaluationKernel.evaluation K a ha (1 + zCoordinate K) ≠ 0
    simp [Order13InfinityEvaluationKernel.evaluation, map_add,
      Order13IntegralSections.reciprocalInfinityEvaluation_z]
  simpa only [map_add, map_one, z] using h

theorem plus_isUnit_at_positive (h2 : (2 : K) ≠ 0) : IsUnit (plus K 1 (positiveProof K)) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K 1 (positiveProof K))
    (infinityIdeal K 1 (positiveProof K)) _).mpr
  change Order13InfinityEvaluationKernel.evaluation K 1 (positiveProof K) (reciprocalPlus K) ≠ 0
  rw [reciprocalPlus_evaluation]
  simpa only [one_add_one_eq_two] using h2

theorem minus_isUnit_at_negative (h2 : (2 : K) ≠ 0) :
    IsUnit (minus K (-1) (negativeProof K)) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K (-1) (negativeProof K))
    (infinityIdeal K (-1) (negativeProof K)) _).mpr
  change Order13InfinityEvaluationKernel.evaluation K (-1) (negativeProof K) (reciprocalMinus K) ≠ 0
  rw [reciprocalMinus_evaluation]
  have heq : (-1 : K) - 1 = -(2 : K) := by ring
  rw [heq]
  exact neg_ne_zero.mpr h2

theorem unitFactor_isUnit (a : K) (ha : a ^ 2 = 1) (h2 : (2 : K) ≠ 0) :
    IsUnit ((-4 : LocalRing K a ha) * (1 + z K a ha)) :=
  (Order13PellInfinityLocalOrders.neg_four_isUnit K a ha h2).mul (one_add_z_isUnit K a ha)

theorem minus_at_positive_associated (h2 : (2 : K) ≠ 0) :
    Associated (minus K 1 (positiveProof K)) (z K 1 (positiveProof K) ^ 2) := by
  apply (associated_mul_isUnit_left_iff (plus_isUnit_at_positive K h2)).mp
  rw [product]
  have heq : -4 * z K 1 (positiveProof K) ^ 2 * (1 + z K 1 (positiveProof K)) =
      (-4 * (1 + z K 1 (positiveProof K))) * z K 1 (positiveProof K) ^ 2 := by ring
  rw [heq]
  exact associated_unit_mul_left _ _ (unitFactor_isUnit K 1 (positiveProof K) h2)

theorem plus_at_negative_associated (h2 : (2 : K) ≠ 0) :
    Associated (plus K (-1) (negativeProof K)) (z K (-1) (negativeProof K) ^ 2) := by
  apply (associated_isUnit_mul_left_iff (minus_isUnit_at_negative K h2)).mp
  rw [product]
  have heq : -4 * z K (-1) (negativeProof K) ^ 2 * (1 + z K (-1) (negativeProof K)) =
      (-4 * (1 + z K (-1) (negativeProof K))) * z K (-1) (negativeProof K) ^ 2 := by ring
  rw [heq]
  exact associated_unit_mul_left _ _ (unitFactor_isUnit K (-1) (negativeProof K) h2)

end MazurTransfer.Order13CubicInfinityLocalOrders
#print axioms MazurTransfer.Order13CubicInfinityLocalOrders.minus_at_positive_associated
#print axioms MazurTransfer.Order13CubicInfinityLocalOrders.plus_at_negative_associated


