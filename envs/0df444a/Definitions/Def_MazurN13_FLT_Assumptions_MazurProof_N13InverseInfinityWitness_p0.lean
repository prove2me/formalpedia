-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InverseInfinityWitness_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InverseInfinityWitness_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:20:38.98031+00:00
-- url     : https://prove2.me/theorems/d5d74e55-5d8f-47a5-8b94-a6a967b91ae9
-- title:
--   FLT.Assumptions.MazurProof.N13InverseInfinityWitness source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InverseInfinityWitness

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InverseInfinityWitness
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InverseInfinityData_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13OppositeInfinityClass_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartPicardRealization_p0

set_option autoImplicit false




/-!
# Candidate nInf = 2 witness: the cusp-pair line with generic infinity integer `-2`

The proper split-quadratic line through `x = 0, -1` (good ordinates `0, 1`) has literal special divisor
`s(zeroPlus, negOnePlus) = C + A` (`N13InverseInfinityData`).  We package it with generic infinity integer
`-2` (= nInf − 1 for the inverse-infinity orientation; the balanced datum `(X(X+1), 1, 0)` would give `-1`,
whose class is `2 •` the target, see `N13OppositeInfinityClass`).

Proved here: the special Abel class, and the exact one-step shift of the generic class
`genericClass L (k - 1) = genericClass L k + classOf (1,0,0)`, so that the generic class of the witness
equals `classOf D_CA - classOf (1,0,2)` whenever `D_CA` realizes the line's affine ideal.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N13InverseInfinityWitness

open N13SplitQuadraticSpecialRestriction MazurProof.N13InverseInfinityData

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The proper cusp-pair line through `(0, 0)` and `(-1, 1)` in good coordinates. -/
abbrev caLine : N13TwoChartPicardRealization.Line :=
  N13QuadraticTwoChartSpread.pairLine
    (0 : N13SplitQuadraticSpecialRestriction.Q₂) (N13TwoChartLineTensor.goodY 0 1)
    (-1) (N13TwoChartLineTensor.goodY (-1) 1) curve_zero curve_negOne

/-- The candidate nInf = 2 two-fibre datum. -/
def inverseInfinityData : N13TwoChartPicardRealization.Data where
  charts := caLine
  infinityOrder := -2
  specialDivisor :=
    s(N13SpecialCuspReduction.specialCuspEquiv .zeroPlus,
      N13SpecialCuspReduction.specialCuspEquiv .negOnePlus)
  special_affine := by
    rw [restrict_pairLine_affineIdeal, reducedPairDivisor_inverseInfinity]
  special_infinity := by
    rw [restrict_pairLine_infinityIdeal, reducedPairDivisor_inverseInfinity]

theorem inverseInfinityData_specialDivisor :
    inverseInfinityData.specialDivisor =
      s(N13SpecialCuspReduction.specialCuspEquiv .zeroPlus,
        N13SpecialCuspReduction.specialCuspEquiv .negOnePlus) := rfl

theorem inverseInfinityData_toSpecialPic :
    inverseInfinityData.toSpecialPic =
      N13AbelFiberTwoModel.abel
        s(N13SpecialCuspReduction.specialCuspEquiv .zeroPlus,
          N13SpecialCuspReduction.specialCuspEquiv .negOnePlus) := rfl

/-- Lowering the generic infinity integer by one adds the negative-infinity class. -/
theorem genericClass_sub_one (L : N13TwoChartPicardRealization.Line) (k : ℤ) :
    N13TwoChartPicardRealization.genericClass L (k - 1) =
      N13TwoChartPicardRealization.genericClass L k +
        SexticMumford.classOf N13TwoChartPicardRealization.Model
          (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂)
          (SexticMumford.infinityMinusMumford N13TwoChartPicardRealization.Model) := by
  have hraw :
      N13TwoChartPicardRealization.genericRaw L (k - 1) =
        N13TwoChartPicardRealization.genericRaw L k *
          SexticMumford.mumfordRaw N13TwoChartPicardRealization.Model
            (SexticMumford.infinityMinusMumford N13TwoChartPicardRealization.Model) := by
    apply Prod.ext
    · change N13TwoChartPicardRealization.genericIdealUnit L =
        N13TwoChartPicardRealization.genericIdealUnit L *
          SexticMumford.mumfordIdealUnit N13TwoChartPicardRealization.Model
            (SexticMumford.infinityMinusMumford N13TwoChartPicardRealization.Model).toSemi
      rw [MazurProof.N13Arithmetic.infinityMinus_idealUnit_one, mul_one]
    · change Multiplicative.ofAdd (k - 1) =
        Multiplicative.ofAdd k * Multiplicative.ofAdd (((0 : ℕ) : ℤ) - 1)
      rw [← ofAdd_add]
      congr 1
  unfold N13TwoChartPicardRealization.genericClass
  rw [hraw, map_mul]
  rfl

/-- The witness's generic class is `genericClass caLine (-1) - classOf (1,0,2)`. -/
theorem inverseInfinityData_toGenericPic :
    inverseInfinityData.toGenericPic =
      N13TwoChartPicardRealization.genericClass caLine (-1) -
        SexticMumford.classOf N13TwoChartPicardRealization.Model
          (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂)
          (MazurProof.N13Arithmetic.oppositeInfinityMumford N13TwoChartPicardRealization.Q₂) := by
  have h := MazurProof.N13Arithmetic.classOf_opposite_add_infinityMinus
    N13TwoChartPicardRealization.Q₂
  have hshift := genericClass_sub_one caLine (-1)
  change N13TwoChartPicardRealization.genericClass caLine (-2) = _
  rw [show (-2 : ℤ) = -1 - 1 by norm_num, hshift]
  rw [eq_neg_of_add_eq_zero_right h, sub_eq_add_neg]

end MazurProof.N13InverseInfinityWitness


