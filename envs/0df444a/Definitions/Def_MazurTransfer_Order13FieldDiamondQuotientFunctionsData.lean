-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldDiamondQuotientFunctionsData
-- name    : MazurTransfer_Order13FieldDiamondQuotientFunctionsData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T17:30:30.607424+00:00
-- url     : https://prove2.me/theorems/d6ee1429-2a88-480f-acb1-d43a6e161141
-- title:
--   Literal diamond quotient functions and cubic orbit norm over characteristic-zero fields
-- statement:
--   The original functions u and v in the actual curve function field over a characteristic-zero field, their diamond transformation and square invariance, conic equation, cubic equation and explicit cubic orbit norm. Nine original declaration types, both actual function values and five original scalar algebra providers are compared. Named downstream consumer: rational conic parameter and exact order-three fixed field.
-- source:
--   Complete original MazurTheorem Order13FieldDiamondQuotientFunctions and literal generic conic identities, using the published actual general-field diamond map and exact order data. Official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal invariant functions in the actual order-thirteen
curve function field, their (cubic K) norm and conic equation. Named downstream
consumer: the order-three quotient and its Picard trace relation. These
identities alone do not identify the invariant field or prove rank zero.
-/
import Definitions.Def_MazurTransfer_Order13FieldDiamondExactOrderData
import Definitions.Def_MazurTransfer_Order13DiamondQuotientConicData

noncomputable section
universe w
namespace MazurTransfer.Order13FieldDiamondQuotientFunctions
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13FieldOrdinaryPolynomialTranscendence
open Order13FieldDiamondFunctionFieldMap Order13FieldDiamondFunctionFieldAutomorphism
open Order13DiamondQuotientConic Order13DiamondSexticSymmetry
variable (K : Type w) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : CharZero (actualCurveFunctionField K) := Algebra.charZero_of_charZero K _

def u : actualCurveFunctionField K := quotientU (xImage K)
def v : actualCurveFunctionField K := quotientV (xImage K) (yImage K)

theorem u_fixed : (diamondFieldMap K) (u K) = (u K) := by
  change (diamondFieldMap K) (quotientU (xImage K)) = quotientU (xImage K)
  simp only [quotientU, map_div₀, map_sub, map_pow, map_mul, map_add,
    map_ofNat, map_one, (diamondFieldMap_x K)]
  exact quotientU_diamond (xImage K) (xImage_ne_zero K) (xImage_add_one_ne_zero K)

theorem v_negated : (diamondFieldMap K) (v K) = -(v K) := by
  change (diamondFieldMap K) (quotientV (xImage K) (yImage K)) = -quotientV (xImage K) (yImage K)
  simp only [quotientV, map_div₀, map_mul, map_add, map_one,
    (diamondFieldMap_x K), (diamondFieldMap_y K)]
  exact quotientV_diamond (xImage K) (yImage K) (xImage_ne_zero K) (xImage_add_one_ne_zero K)

theorem square_fixes_u : (diamondSecond K) (u K) = (u K) := by
  change (diamondFieldMap K) ((diamondFieldMap K) (u K)) = (u K)
  rw [(u_fixed K), (u_fixed K)]

theorem square_fixes_v : (diamondSecond K) (v K) = (v K) := by
  change (diamondFieldMap K) ((diamondFieldMap K) (v K)) = (v K)
  rw [(v_negated K), map_neg, (v_negated K), neg_neg]

theorem conic_equation : (v K) ^ 2 = (u K) ^ 2 + 2 * (u K) + 5 :=
  quotient_conic (xImage K) (yImage K) (xImage_ne_zero K) (xImage_add_one_ne_zero K) (yImage_sq K)

theorem cubic_equation : fiberCubic (u K) (xImage K) = 0 :=
  fiberCubic_quotientU (xImage K) (xImage_ne_zero K) (xImage_add_one_ne_zero K)

theorem cubic_orbit_norm (z : actualCurveFunctionField K) :
    (z - xImage K) * (z - (diamondFieldMap K) (xImage K)) *
      (z - (diamondSecond K) (xImage K)) = fiberCubic (u K) z := by
  rw [(diamondFieldMap_x K)]
  change (z - xImage K) * (z - diamondX (xImage K)) *
    (z - (diamondFieldMap K) ((diamondFieldMap K) (xImage K))) = fiberCubic (u K) z
  rw [(diamondFieldMap_x K), (map_diamondX K), (diamondFieldMap_x K)]
  exact orbit_norm (xImage K) z (xImage_ne_zero K) (xImage_add_one_ne_zero K)

end MazurTransfer.Order13FieldDiamondQuotientFunctions
#print axioms MazurTransfer.Order13FieldDiamondQuotientFunctions.conic_equation
#print axioms MazurTransfer.Order13FieldDiamondQuotientFunctions.cubic_orbit_norm


