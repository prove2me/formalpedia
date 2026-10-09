-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InverseInfinityData_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InverseInfinityData_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:17:38.767099+00:00
-- url     : https://prove2.me/theorems/7348394c-fe42-418c-8884-4b116d5801ec
-- title:
--   FLT.Assumptions.MazurProof.N13InverseInfinityData source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InverseInfinityData

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InverseInfinityData
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SplitQuadraticSpecialRestriction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialCuspReduction_p0

set_option autoImplicit false




/-!
# Special divisor of the nInf = 2 degree-zero witness

The split quadratic u = X(X+1), v = 1 has roots x = 0, -1 with good ordinates 0 and 1; its literal reduced
special divisor is s(zeroPlus, negOnePlus) = C + A (cf. N13CuspCARelation: AJ13 C + AJ13 A = -AJ13 T).
This corrects the D + B divisor guessed in ChatGPT answer Q8689.
-/

namespace MazurProof.N13InverseInfinityData

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

open N13SplitQuadraticSpecialRestriction

abbrev Q₂ : Type := N13SplitQuadraticSpecialRestriction.Q₂

theorem goodY_zero_one : N13TwoChartLineTensor.goodY (0 : Q₂) 1 = 0 := by
  simp [N13TwoChartLineTensor.goodY, N13GoodModelTwo.h]

theorem goodY_negOne_one : N13TwoChartLineTensor.goodY (-1 : Q₂) 1 = 1 := by
  simp [N13TwoChartLineTensor.goodY, N13GoodModelTwo.h]; norm_num

theorem curve_zero : N13GoodModelTwo.AffineEquation (0 : Q₂) (N13TwoChartLineTensor.goodY 0 1) := by
  rw [goodY_zero_one]; simp [N13GoodModelTwo.AffineEquation, N13GoodModelTwo.h, N13GoodModelTwo.rhs]

theorem curve_negOne : N13GoodModelTwo.AffineEquation (-1 : Q₂) (N13TwoChartLineTensor.goodY (-1) 1) := by
  rw [goodY_negOne_one]; norm_num [N13GoodModelTwo.AffineEquation, N13GoodModelTwo.h, N13GoodModelTwo.rhs]



theorem toZMod_mk_of_eq (y c : Q₂) (h : ‖y‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hy : y = c) :
    PadicInt.toZMod (⟨y, h⟩ : ℤ_[2]) = PadicInt.toZMod (⟨c, hc⟩ : ℤ_[2]) := by
  subst hy; rfl

theorem reducedPoint_zero :
    reducedPoint (0 : Q₂) (N13TwoChartLineTensor.goodY 0 1) curve_zero =
      N13SpecialCuspReduction.specialCuspEquiv .zeroPlus := by
  apply N13AbelFiberTwoModel.curvePointEquiv.injective
  have hx : ‖(0 : Q₂)‖ ≤ 1 := by simp
  rw [reducedPoint, dif_pos hx, N13IntegralAffinePointSpecialClass.curvePointEquiv_reducedPoint,
    N13SpecialCuspReduction.curvePointEquiv_specialCuspEquiv]
  simp only [N13SpecialCuspReduction.cuspCoordinate, N13ProperCurveReduction.integralAffineLift]
  ext
  · simp
  · show PadicInt.toZMod _ = 0
    rw [toZMod_mk_of_eq _ 0 _ (by simp) goodY_zero_one]
    exact map_zero _

theorem reducedPoint_negOne :
    reducedPoint (-1 : Q₂) (N13TwoChartLineTensor.goodY (-1) 1) curve_negOne =
      N13SpecialCuspReduction.specialCuspEquiv .negOnePlus := by
  apply N13AbelFiberTwoModel.curvePointEquiv.injective
  have hx : ‖(-1 : Q₂)‖ ≤ 1 := by simp
  rw [reducedPoint, dif_pos hx, N13IntegralAffinePointSpecialClass.curvePointEquiv_reducedPoint,
    N13SpecialCuspReduction.curvePointEquiv_specialCuspEquiv]
  simp only [N13SpecialCuspReduction.cuspCoordinate, N13ProperCurveReduction.integralAffineLift]
  ext
  · simp
  · show PadicInt.toZMod _ = 1
    rw [toZMod_mk_of_eq _ 1 _ (by simp) goodY_negOne_one]
    exact map_one _

theorem reducedPairDivisor_inverseInfinity :
    reducedPairDivisor (0 : Q₂) (N13TwoChartLineTensor.goodY 0 1)
        (-1) (N13TwoChartLineTensor.goodY (-1) 1) curve_zero curve_negOne =
      s(N13SpecialCuspReduction.specialCuspEquiv .zeroPlus,
        N13SpecialCuspReduction.specialCuspEquiv .negOnePlus) := by
  rw [reducedPairDivisor, reducedPoint_zero, reducedPoint_negOne]


end
end MazurProof.N13InverseInfinityData


