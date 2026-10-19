-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualConicFunctionParameterData
-- name    : MazurTransfer_Order13ActualConicFunctionParameterData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T16:20:14.423034+00:00
-- url     : https://prove2.me/theorems/5b75d50b-fec3-4bcb-baf9-7ef30640afea
-- title:
--   Actual rational conic function parameter and recovered coordinates
-- statement:
--   The original actual slope parameter t is retained with its nonvanishing denominator certificate, both recovered conic coordinates, diamond-square fixedness and recovered y coordinate. Seven full original types and the original parameter value are checked; the original local rational algebra provider is separately checked in type and value. Only proof-valued dependency Fact instances are expanded. Named downstream consumer: actual cubic extension and rational fixed field.
-- source:
--   Unchanged original MazurTheorem Order13ActualConicFunctionParameter declarations and proof bodies, Apache-2.0, Vas and contributors. Public generic conic formulas and the original actual diamond function-field automorphism supply the dependencies; all original full types and non-proof data values are kernel-compared.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual quotient conic has a literal rational function
parameter, with both conic coordinates recovered. Named downstream consumer:
the degree-three fixed field and the Picard trace relation for the descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualDiamondQuotientFunctionsData
import Definitions.Def_MazurTransfer_RationalConicFunctionParameterData

noncomputable section
namespace MazurTransfer.Order13ActualConicFunctionParameter
open Polynomial
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ActualOrdinaryPolynomialTranscendence
open Order13ActualDiamondFunctionFieldAutomorphism Order13ActualDiamondQuotientFunctions
open Order13DiamondQuotientConic RationalConicFunctionParameter
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : CharZero (actualCurveFunctionField ℚ) := algebraRat.charZero _
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem u_add_one_ne_zero : u + 1 ≠ 0 := by
  intro H
  have Hu : u = -1 := by linear_combination H
  have Hc := cubic_equation
  rw [Hu] at Hc
  simp only [fiberCubic] at Hc
  have Hr : xImage ℚ ^ 3 + xImage ℚ ^ 2 - 2 * xImage ℚ - 1 = 0 := by
    linear_combination Hc
  apply xImage_transcendental
  refine ⟨X ^ 3 + X ^ 2 - C 2 * X - 1, ?_, ?_⟩
  · intro Hp
    have H3 := congrArg (fun p : Polynomial ℚ => p.coeff 3) Hp
    norm_num [Polynomial.coeff_X, Polynomial.coeff_one] at H3
  · simpa only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one,
      aeval_X, aeval_C, map_natCast] using Hr

def t : actualCurveFunctionField ℚ := slope u v

theorem t_sq_ne_one : t ^ 2 ≠ 1 := slope_sq_ne_one u v u_add_one_ne_zero conic_equation
theorem u_parameter : conicU t = u := (parameter_inverse u v u_add_one_ne_zero conic_equation).2.1
theorem v_parameter : conicV t = v := (parameter_inverse u v u_add_one_ne_zero conic_equation).2.2

theorem square_fixes_parameter : diamondSecond t = t := by
  change diamondSecond (slope u v) = slope u v
  simp only [RationalConicFunctionParameter.slope, map_div₀, map_sub, map_add, map_one, map_ofNat,
    square_fixes_u, square_fixes_v]

theorem y_recovered : yImage ℚ = v * (xImage ℚ * (xImage ℚ + 1)) := by
  change yImage ℚ = (yImage ℚ / (xImage ℚ * (xImage ℚ + 1))) * _
  exact (div_mul_cancel₀ _ (mul_ne_zero xImage_ne_zero xImage_add_one_ne_zero)).symm

end MazurTransfer.Order13ActualConicFunctionParameter
#print axioms MazurTransfer.Order13ActualConicFunctionParameter.u_parameter
#print axioms MazurTransfer.Order13ActualConicFunctionParameter.square_fixes_parameter


