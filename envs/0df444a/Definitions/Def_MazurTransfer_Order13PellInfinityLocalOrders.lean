-- Prove2me | Definitions.Def_MazurTransfer_Order13PellInfinityLocalOrders
-- name    : MazurTransfer_Order13PellInfinityLocalOrders
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T12:01:52.674964+00:00
-- url     : https://prove2.me/theorems/501d3579-29f8-4077-a730-160cfe810ea2
-- title:
--   The exact local orders of the reciprocal Pell factors at infinity
-- statement:
--   Over a field of characteristic zero, the original reciprocal Pell factors in the actual infinity local rings have orders $$\operatorname{ord}_{+}(P_{\infty,+})=0,\quad\operatorname{ord}_{-}(P_{\infty,+})=38,\qquad\operatorname{ord}_{-}(P_{\infty,-})=0,\quad\operatorname{ord}_{+}(P_{\infty,-})=38.$$ The local reciprocal coordinate is irreducible, and the original factor product and unit certificates are retained. Dividing by its nineteenth power yields the degree-nineteen Pell principal divisor in the downstream function-field identification.
-- source:
--   Original complete fourteen declarations from MazurTheorem Order13PellInfinityLocalOrders.lean, with the short original infinity-coordinate irreducibility consequence inlined unchanged, Apache-2.0, Vas and contributors. Fifteen complete original closed types and two data values are kernel-compared. All original bodies are unchanged; explicit local DVR instances consume the separately Proved original DVR contract. Named downstream consumer: actual Pell infinity valuations and principal divisor.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual normalized Pell numerators have orders 0 and 38
in the two reciprocal-chart discrete valuation rings. Named downstream
consumer: after dividing by z^19, the degree-19 Pell principal divisor.
The global function-field and divisor identifications are separate work.
-/
import Definitions.Def_MazurTransfer_Order13PellInfinityFactorEvaluations
import Definitions.Def_MazurTransfer_Order13InfinityLocalRingDomain
import Theorems.Thm_MazurTransfer_Order13InfinityLocalParameter_maximalIdeal_eq_span_z
import Theorems.Thm_MazurTransfer_Order13InfinityDiscreteValuationRing_localRing_isDiscreteValuationRing
noncomputable section
universe u
namespace MazurTransfer.Order13InfinityDiscreteValuationRing
open MazurTransfer.Order13InfinityLocalParameter
variable (K : Type u) [Field K] [CharZero K] (a : K) (ha : a ^ 2 = 1)
local instance : IsDiscreteValuationRing (LocalRing K a ha) := localRing_isDiscreteValuationRing K a ha
theorem z_irreducible : Irreducible (z K a ha) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (maximalIdeal_eq_span_z K a ha (by norm_num))

end MazurTransfer.Order13InfinityDiscreteValuationRing


noncomputable section
namespace MazurTransfer.Order13PellInfinityLocalOrders
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13InfinityLocalParameter
open Order13PellChartCertificate
variable (K : Type u) [Field K]

theorem positiveProof : (1 : K) ^ 2 = 1 := by simp
theorem negativeProof : (-1 : K) ^ 2 = 1 := by simp

def plus (a : K) (ha : a ^ 2 = 1) : LocalRing K a ha :=
  algebraMap (ReciprocalRing K) (LocalRing K a ha) (reciprocalPlus K)

def minus (a : K) (ha : a ^ 2 = 1) : LocalRing K a ha :=
  algebraMap (ReciprocalRing K) (LocalRing K a ha) (reciprocalMinus K)

theorem product (a : K) (ha : a ^ 2 = 1) :
    plus K a ha * minus K a ha = -4 * z K a ha ^ 38 := by
  have h := congrArg (algebraMap (ReciprocalRing K) (LocalRing K a ha)) (reciprocal_product K)
  simpa only [plus, minus, z, map_mul, map_neg, _root_.map_ofNat, map_pow] using h

theorem plus_isUnit_at_positive (h2 : (2 : K) ≠ 0) :
    IsUnit (plus K 1 (positiveProof K)) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K 1 (positiveProof K))
    (infinityIdeal K 1 (positiveProof K)) _).mpr
  change Order13InfinityEvaluationKernel.evaluation K 1 (positiveProof K) (reciprocalPlus K) ≠ 0
  rw [reciprocalPlus_evaluation]
  simpa only [sub_neg_eq_add, one_add_one_eq_two] using h2

theorem minus_isUnit_at_negative (h2 : (2 : K) ≠ 0) :
    IsUnit (minus K (-1) (negativeProof K)) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K (-1) (negativeProof K))
    (infinityIdeal K (-1) (negativeProof K)) _).mpr
  change Order13InfinityEvaluationKernel.evaluation K (-1) (negativeProof K) (reciprocalMinus K) ≠ 0
  rw [reciprocalMinus_evaluation]
  simpa only [sub_neg_eq_add, one_add_one_eq_two] using h2

theorem neg_four_isUnit (a : K) (ha : a ^ 2 = 1) (h2 : (2 : K) ≠ 0) :
    IsUnit (-4 : LocalRing K a ha) := by
  have h := ((isUnit_iff_ne_zero.mpr h2).map
    ((algebraMap (ReciprocalRing K) (LocalRing K a ha)).comp
      (algebraMap K (ReciprocalRing K)))).pow 2
  have heq : (2 : LocalRing K a ha) ^ 2 = 4 := by ring
  simpa only [RingHom.comp_apply, _root_.map_ofNat, heq] using h.neg

theorem plus_at_negative_associated (h2 : (2 : K) ≠ 0) :
    Associated (plus K (-1) (negativeProof K)) (z K (-1) (negativeProof K) ^ 38) := by
  apply (associated_mul_isUnit_left_iff (minus_isUnit_at_negative K h2)).mp
  rw [product]
  exact associated_unit_mul_left _ _ (neg_four_isUnit K (-1) (negativeProof K) h2)

theorem minus_at_positive_associated (h2 : (2 : K) ≠ 0) :
    Associated (minus K 1 (positiveProof K)) (z K 1 (positiveProof K) ^ 38) := by
  apply (associated_isUnit_mul_left_iff (plus_isUnit_at_positive K h2)).mp
  rw [product]
  exact associated_unit_mul_left _ _ (neg_four_isUnit K 1 (positiveProof K) h2)

section CharacteristicZero
variable [CharZero K]
local instance (a : K) (ha : a ^ 2 = 1) : IsDiscreteValuationRing (LocalRing K a ha) :=
  Order13InfinityDiscreteValuationRing.localRing_isDiscreteValuationRing K a ha

theorem plus_addVal_at_positive :
    IsDiscreteValuationRing.addVal (LocalRing K 1 (positiveProof K)) (plus K 1 (positiveProof K)) = 0 :=
  IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (plus_isUnit_at_positive K (by norm_num))

theorem minus_addVal_at_negative :
    IsDiscreteValuationRing.addVal (LocalRing K (-1) (negativeProof K)) (minus K (-1) (negativeProof K)) = 0 :=
  IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (minus_isUnit_at_negative K (by norm_num))

theorem plus_addVal_at_negative :
    IsDiscreteValuationRing.addVal (LocalRing K (-1) (negativeProof K)) (plus K (-1) (negativeProof K)) = 38 := by
  rw [(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr
    (plus_at_negative_associated K (by norm_num))]
  exact (Order13InfinityDiscreteValuationRing.z_irreducible K (-1) (negativeProof K)).addVal_pow 38

theorem minus_addVal_at_positive :
    IsDiscreteValuationRing.addVal (LocalRing K 1 (positiveProof K)) (minus K 1 (positiveProof K)) = 38 := by
  rw [(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr
    (minus_at_positive_associated K (by norm_num))]
  exact (Order13InfinityDiscreteValuationRing.z_irreducible K 1 (positiveProof K)).addVal_pow 38

end CharacteristicZero
end MazurTransfer.Order13PellInfinityLocalOrders
#print axioms MazurTransfer.Order13PellInfinityLocalOrders.plus_addVal_at_positive
#print axioms MazurTransfer.Order13PellInfinityLocalOrders.plus_addVal_at_negative
#print axioms MazurTransfer.Order13PellInfinityLocalOrders.minus_addVal_at_negative
#print axioms MazurTransfer.Order13PellInfinityLocalOrders.minus_addVal_at_positive


