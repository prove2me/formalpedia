-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldConicFunctionParameterData
-- name    : MazurTransfer_Order13FieldConicFunctionParameterData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T17:36:40.483918+00:00
-- url     : https://prove2.me/theorems/908bf744-b6f8-4d0f-ad3e-76c4e2ef801e
-- title:
--   The literal diamond quotient conic has a rational parameter over characteristic-zero fields
-- statement:
--   The original slope parameter in the actual curve function field, nonzero denominators, recovery of both conic coordinates, invariance under the diamond square and recovery of the original ordinate, over every characteristic-zero field. Seven full original types, the parameter data value and six original current/dependency scalar algebra providers are compared. Named downstream consumer: exact cubic extension and rational order-three fixed field.
-- source:
--   Complete original MazurTheorem Order13FieldConicFunctionParameter, with published generic rational-conic parametrization and literal quotient functions. Official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual quotient conic has a literal rational function
parameter, with both conic coordinates recovered. Named downstream consumer:
the degree-three fixed field and the Picard trace relation for the descent.
-/
import Definitions.Def_MazurTransfer_Order13FieldDiamondQuotientFunctionsData
import Definitions.Def_MazurTransfer_RationalConicFunctionParameterData

noncomputable section
universe w
namespace MazurTransfer.Order13FieldConicFunctionParameter
open Polynomial
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13FieldOrdinaryPolynomialTranscendence
open Order13FieldDiamondFunctionFieldAutomorphism Order13FieldDiamondQuotientFunctions
open Order13DiamondQuotientConic RationalConicFunctionParameter
variable (K : Type w) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : CharZero (actualCurveFunctionField K) := Algebra.charZero_of_charZero K _

theorem u_add_one_ne_zero : (u K) + 1 ≠ 0 := by
  intro H
  have Hu : (u K) = -1 := by linear_combination H
  have Hc := (cubic_equation K)
  rw [Hu] at Hc
  simp only [fiberCubic] at Hc
  have Hr : xImage K ^ 3 + xImage K ^ 2 - 2 * xImage K - 1 = 0 := by
    linear_combination Hc
  apply (xImage_transcendental K)
  refine ⟨X ^ 3 + X ^ 2 - C 2 * X - 1, ?_, ?_⟩
  · intro Hp
    have H3 := congrArg (fun p : Polynomial K => p.coeff 3) Hp
    norm_num [Polynomial.coeff_X, Polynomial.coeff_one] at H3
  · simpa only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one,
      aeval_X, aeval_C, map_natCast] using Hr

def t : actualCurveFunctionField K := slope (u K) (v K)

theorem t_sq_ne_one : (t K) ^ 2 ≠ 1 := slope_sq_ne_one (u K) (v K) (u_add_one_ne_zero K) (conic_equation K)
theorem u_parameter : conicU (t K) = (u K) := (parameter_inverse (u K) (v K) (u_add_one_ne_zero K) (conic_equation K)).2.1
theorem v_parameter : conicV (t K) = (v K) := (parameter_inverse (u K) (v K) (u_add_one_ne_zero K) (conic_equation K)).2.2

theorem square_fixes_parameter : (diamondSecond K) (t K) = (t K) := by
  change (diamondSecond K) (slope (u K) (v K)) = slope (u K) (v K)
  simp only [RationalConicFunctionParameter.slope, map_div₀, map_sub, map_add, map_one, map_ofNat,
    (square_fixes_u K), (square_fixes_v K)]

theorem y_recovered : yImage K = (v K) * (xImage K * (xImage K + 1)) := by
  change yImage K = (yImage K / (xImage K * (xImage K + 1))) * _
  exact (div_mul_cancel₀ _ (mul_ne_zero (xImage_ne_zero K) (xImage_add_one_ne_zero K))).symm

end MazurTransfer.Order13FieldConicFunctionParameter
#print axioms MazurTransfer.Order13FieldConicFunctionParameter.u_parameter
#print axioms MazurTransfer.Order13FieldConicFunctionParameter.square_fixes_parameter


