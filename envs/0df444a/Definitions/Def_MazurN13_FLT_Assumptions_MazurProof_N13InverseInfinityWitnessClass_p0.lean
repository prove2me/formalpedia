-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InverseInfinityWitnessClass_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InverseInfinityWitnessClass_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:23:10.592509+00:00
-- url     : https://prove2.me/theorems/26a24261-dc3e-461a-b7f7-089cff246f40
-- title:
--   FLT.Assumptions.MazurProof.N13InverseInfinityWitnessClass source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InverseInfinityWitnessClass

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InverseInfinityWitnessClass
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InverseInfinityWitness_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityBaseChange_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuadraticTwoChartSpreadSaturation_p0

set_option autoImplicit false




/-!
# Generic class of the nInf = 2 witness

`inverseInfinityData` (cusp-pair line, generic infinity integer `-2`, special divisor `C + A`) has generic class
`classOf (1,0,2)` over `Q₂`: its raw datum is `raw C₂ * raw A₂`, and over `ℚ` `AJ13 C + AJ13 A = classOf (1,0,2)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace MazurProof.N13InverseInfinityWitness

open Polynomial MazurProof.N13Arithmetic

local instance instFactPrimeOfNatNat_fLT_1 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Base change of a rational balanced representative. -/
abbrev mapQ₂ (D : N13Mumford.Mumford ℚ) : N13Mumford.Mumford N13InfinityBaseChange.Q₂ :=
  D.mapCoeffs N13InfinityBaseChange.ratToQ₂ N13InfinityBaseChange.ratToQ₂_injective
    (N13InfinityBaseChange.map_n13_f N13InfinityBaseChange.ratToQ₂)

abbrev cRat : N13Mumford.Mumford ℚ :=
  SexticMumford.pointMumford (N13Mumford.model ℚ) (point13EquivCurvePoint C)

abbrev aRat : N13Mumford.Mumford ℚ :=
  SexticMumford.pointMumford (N13Mumford.model ℚ) (point13EquivCurvePoint A)

theorem cRat_u : cRat.u = (X : ℚ[X]) := by
  change X - Polynomial.C (0 : ℚ) = X
  simp

theorem cRat_v : cRat.v = (1 : ℚ[X]) := by
  change Polynomial.C (1 : ℚ) = (1 : ℚ[X])
  norm_num

theorem aRat_u : aRat.u = (X + 1 : ℚ[X]) := by
  change X - Polynomial.C (-1 : ℚ) = X + 1
  simp

theorem aRat_v : aRat.v = (1 : ℚ[X]) := by
  change Polynomial.C (1 : ℚ) = (1 : ℚ[X])
  norm_num

theorem genericIdealUnit_caLine :
    N13TwoChartPicardRealization.genericIdealUnit caLine =
      SexticMumford.mumfordIdealUnit N13TwoChartPicardRealization.Model (mapQ₂ cRat).toSemi *
        SexticMumford.mumfordIdealUnit N13TwoChartPicardRealization.Model (mapQ₂ aRat).toSemi := by
  apply Units.ext
  rw [Units.val_mul, N13TwoChartPicardRealization.coe_genericIdealUnit,
    SexticMumford.coe_mumfordIdealUnit, SexticMumford.coe_mumfordIdealUnit,
    ← FractionalIdeal.coeIdeal_mul]
  congr 1
  have h := N13QuadraticTwoChartSpread.map_pairLine_affineIdeal
    (0 : N13SplitQuadraticSpecialRestriction.Q₂) (N13TwoChartLineTensor.goodY 0 1)
    (-1) (N13TwoChartLineTensor.goodY (-1) 1)
    MazurProof.N13InverseInfinityData.curve_zero MazurProof.N13InverseInfinityData.curve_negOne
  rw [N13TwoChartLineTensor.pointY_goodY, N13TwoChartLineTensor.pointY_goodY] at h
  refine h.trans ?_
  simp only [mapQ₂, SexticMumford.toSemi_u, SexticMumford.toSemi_v, SexticMumford.mapCoeffs_u,
    SexticMumford.mapCoeffs_v, cRat_u, cRat_v, aRat_u, aRat_v, Polynomial.map_X, Polynomial.map_one,
    Polynomial.map_add]
  simp

theorem mapQ₂_oppositeInfinity :
    mapQ₂ (oppositeInfinityMumford ℚ) = oppositeInfinityMumford N13InfinityBaseChange.Q₂ := by
  have hu : (mapQ₂ (oppositeInfinityMumford ℚ)).u = (oppositeInfinityMumford N13InfinityBaseChange.Q₂).u := by
    simp [mapQ₂, oppositeInfinityMumford]
  have hv : (mapQ₂ (oppositeInfinityMumford ℚ)).v = (oppositeInfinityMumford N13InfinityBaseChange.Q₂).v := by
    simp [mapQ₂, oppositeInfinityMumford]
  have hn : (mapQ₂ (oppositeInfinityMumford ℚ)).nInf =
      (oppositeInfinityMumford N13InfinityBaseChange.Q₂).nInf := rfl
  generalize mapQ₂ (oppositeInfinityMumford ℚ) = D at hu hv hn
  cases D
  simp_all [oppositeInfinityMumford]

/-- **The nInf = 2 witness realizes the opposite-infinity class.** -/
theorem inverseInfinityData_toGenericPic_eq_opposite :
    inverseInfinityData.toGenericPic =
      SexticMumford.classOf N13TwoChartPicardRealization.Model
        (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂)
        (oppositeInfinityMumford N13TwoChartPicardRealization.Q₂) := by
  have hraw :
      N13TwoChartPicardRealization.genericRaw caLine (-2) =
        SexticMumford.mumfordRaw N13TwoChartPicardRealization.Model (mapQ₂ cRat) *
          SexticMumford.mumfordRaw N13TwoChartPicardRealization.Model (mapQ₂ aRat) := by
    apply Prod.ext
    · exact genericIdealUnit_caLine
    · change Multiplicative.ofAdd (-2 : ℤ) =
        Multiplicative.ofAdd (((0 : ℕ) : ℤ) - 1) * Multiplicative.ofAdd (((0 : ℕ) : ℤ) - 1)
      decide
  have hsum :
      inverseInfinityData.toGenericPic =
        SexticMumford.classOf N13TwoChartPicardRealization.Model
            (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂) (mapQ₂ cRat) +
          SexticMumford.classOf N13TwoChartPicardRealization.Model
            (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂) (mapQ₂ aRat) := by
    change N13TwoChartPicardRealization.genericClass caLine (-2) = _
    unfold N13TwoChartPicardRealization.genericClass
    rw [hraw, map_mul]
    rfl
  have hC : SexticMumford.classOf N13TwoChartPicardRealization.Model
      (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂) (mapQ₂ cRat) =
        N13InfinityBaseChange.picMapRatToQ₂ (AJ13 C) := by
    rw [show AJ13 C = SexticMumford.classOf (N13Mumford.model ℚ)
      (N13Infinity.positiveInfinityOrder ℚ) cRat from rfl, N13InfinityBaseChange.picMapRatToQ₂_classOf]
  have hA : SexticMumford.classOf N13TwoChartPicardRealization.Model
      (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂) (mapQ₂ aRat) =
        N13InfinityBaseChange.picMapRatToQ₂ (AJ13 A) := by
    rw [show AJ13 A = SexticMumford.classOf (N13Mumford.model ℚ)
      (N13Infinity.positiveInfinityOrder ℚ) aRat from rfl, N13InfinityBaseChange.picMapRatToQ₂_classOf]
  rw [hsum, hC, hA, ← map_add, AJ13_C_add_A_eq_classOf_opposite,
    N13InfinityBaseChange.picMapRatToQ₂_classOf]
  exact congrArg _ mapQ₂_oppositeInfinity

/-- The witness's affine lattice is vertically saturated (pair line certificate). -/
theorem inverseInfinityData_affineVerticallySaturated :
    N13TwoChartPicardRealization.AffineVerticallySaturated inverseInfinityData.charts :=
  N13QuadraticTwoChartSpreadSaturation.pairLine_affineVerticallySaturated
    (0 : N13SplitQuadraticSpecialRestriction.Q₂) (N13TwoChartLineTensor.goodY 0 1)
    (-1) (N13TwoChartLineTensor.goodY (-1) 1)
    MazurProof.N13InverseInfinityData.curve_zero MazurProof.N13InverseInfinityData.curve_negOne

end MazurProof.N13InverseInfinityWitness


