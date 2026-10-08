-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OppositeInfinityClass_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13OppositeInfinityClass_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:44:13.200699+00:00
-- url     : https://prove2.me/theorems/076f3d5c-5a58-4d48-a9d7-9a389a7e18b0
-- title:
--   FLT.Assumptions.MazurProof.N13OppositeInfinityClass source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13OppositeInfinityClass

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13OppositeInfinityClass
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CuspCARelation_p0

set_option autoImplicit false




/-!
# The opposite-infinity class and the cusp pair `C + A` (nInf = 2 orientation)

`oppositeInfinityMumford K = (1, 0, 2)` is the balanced representative of the
inverse of the negative-infinity class.  Over `ℚ` we show

* `classOf (1,0,2) = -AJ13 T`, and hence
* `AJ13 C + AJ13 A = classOf (1,0,2)`,

i.e. the cusp pair `C + A` carries the nInf = 2 class.  (Note: the balanced
Mumford datum with `u = X (X + 1)`, `v = 1`, `nInf = 0` has raw infinity
integer `-1`, while `rawC * rawA` has infinity integer `-2`; so its class is
`2 • classOf (1,0,2)`, not `classOf (1,0,2)`.  A coherent nInf = 2 witness must
use the cusp-pair ideal with infinity integer `-2`.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13Arithmetic

/-- The balanced representative `(1, 0, 2)`: the inverse of the
negative-infinity class (base point `∞₊`). -/
def oppositeInfinityMumford (K : Type*) [Field K] [CharZero K] :
    SexticMumford.Mumford (N13Mumford.model K) where
  u := 1
  v := 0
  nInf := 2
  u_monic := monic_one
  deg_u := by simp
  v_reduced := by simp
  curve_dvd := one_dvd _
  infinity_bound := by simp

theorem oppositeInfinity_idealUnit_one (K : Type*) [Field K] [CharZero K] :
    SexticMumford.mumfordIdealUnit (N13Mumford.model K)
        (oppositeInfinityMumford K).toSemi = 1 := by
  apply Units.ext
  change
    (SexticMumford.mumfordIdeal (N13Mumford.model K) 1 0 :
        FractionalIdeal
          (N13Mumford.CoordinateRing K)⁰
          (N13Mumford.FunctionField K)) = 1
  have hz := SexticMumford.zero_mumfordIdeal (N13Mumford.model K)
  change SexticMumford.mumfordIdeal (N13Mumford.model K) 1 0 = ⊤ at hz
  rw [hz]
  rfl

theorem infinityMinus_idealUnit_one (K : Type*) [Field K] [CharZero K] :
    SexticMumford.mumfordIdealUnit (N13Mumford.model K)
        (SexticMumford.infinityMinusMumford (N13Mumford.model K)).toSemi = 1 := by
  apply Units.ext
  change
    (SexticMumford.mumfordIdeal (N13Mumford.model K) 1 0 :
        FractionalIdeal
          (N13Mumford.CoordinateRing K)⁰
          (N13Mumford.FunctionField K)) = 1
  have hz := SexticMumford.zero_mumfordIdeal (N13Mumford.model K)
  change SexticMumford.mumfordIdeal (N13Mumford.model K) 1 0 = ⊤ at hz
  rw [hz]
  rfl

/-- `classOf (1,0,2) + classOf (1,0,0) = 0` over any field. -/
theorem classOf_opposite_add_infinityMinus (K : Type*) [Field K] [CharZero K] :
    SexticMumford.classOf (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) (oppositeInfinityMumford K) +
      SexticMumford.classOf (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K)
        (SexticMumford.infinityMinusMumford (N13Mumford.model K)) = 0 := by
  change Additive.ofMul
      (QuotientGroup.mk' _
        (SexticMumford.mumfordRaw (N13Mumford.model K) (oppositeInfinityMumford K) *
          SexticMumford.mumfordRaw (N13Mumford.model K)
            (SexticMumford.infinityMinusMumford (N13Mumford.model K)))) = 0
  have hraw :
      SexticMumford.mumfordRaw (N13Mumford.model K) (oppositeInfinityMumford K) *
          SexticMumford.mumfordRaw (N13Mumford.model K)
            (SexticMumford.infinityMinusMumford (N13Mumford.model K)) = 1 := by
    apply Prod.ext
    · change
        SexticMumford.mumfordIdealUnit (N13Mumford.model K)
            (oppositeInfinityMumford K).toSemi *
          SexticMumford.mumfordIdealUnit (N13Mumford.model K)
            (SexticMumford.infinityMinusMumford (N13Mumford.model K)).toSemi = 1
      rw [oppositeInfinity_idealUnit_one, infinityMinus_idealUnit_one, mul_one]
    · change Multiplicative.ofAdd (((2 : ℕ) : ℤ) - 1) *
          Multiplicative.ofAdd (((0 : ℕ) : ℤ) - 1) = 1
      decide
  rw [hraw, map_one]
  rfl

theorem classOf_opposite_eq_neg_AJ13_T :
    SexticMumford.classOf (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ) (oppositeInfinityMumford ℚ) =
      -AJ13 T := by
  have h := classOf_opposite_add_infinityMinus ℚ
  have hT : AJ13 T =
      SexticMumford.classOf (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ)
        (SexticMumford.infinityMinusMumford (N13Mumford.model ℚ)) := rfl
  rw [hT]
  exact eq_neg_of_add_eq_zero_left h

/-- The cusp pair `C + A` carries the nInf = 2 (opposite-infinity) class. -/
theorem AJ13_C_add_A_eq_classOf_opposite :
    AJ13 C + AJ13 A =
      SexticMumford.classOf (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ) (oppositeInfinityMumford ℚ) := by
  rw [classOf_opposite_eq_neg_AJ13_T, AJ13_C_add_A_eq_neg_T]

end MazurProof.N13Arithmetic


