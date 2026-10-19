-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDiamondQuotientFunctionsData
-- name    : MazurTransfer_Order13ActualDiamondQuotientFunctionsData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T16:19:06.19013+00:00
-- url     : https://prove2.me/theorems/d80d0052-1a2b-49e5-9193-239ed9413537
-- title:
--   Actual diamond quotient functions and their conic and orbit identities
-- statement:
--   The original actual quotient functions u and v in the literal rational curve function field are retained, with the original diamond invariance/sign, diamond-square fixedness, conic equation, cubic equation and three-factor orbit norm. Nine full original types and two data values are checked, normalizing only named original dependency Fact instances whose types are checked proof-valued. Named downstream consumer: actual rational conic parameter and cubic fixed-field identification.
-- source:
--   Unchanged original MazurTheorem Order13ActualDiamondQuotientFunctions declarations and proof bodies, Apache-2.0, Vas and contributors. Public generic conic formulas and the original actual diamond function-field automorphism supply the dependencies; all original full types and non-proof data values are kernel-compared.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal invariant functions in the actual order-thirteen
curve function field, their cubic norm and conic equation. Named downstream
consumer: the order-three quotient and its Picard trace relation. These
identities alone do not identify the invariant field or prove rank zero.
-/
import Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism
import Definitions.Def_MazurTransfer_Order13DiamondQuotientConicData

noncomputable section
namespace MazurTransfer.Order13ActualDiamondQuotientFunctions
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ActualOrdinaryPolynomialTranscendence
open Order13ActualDiamondFunctionFieldMap Order13ActualDiamondFunctionFieldAutomorphism
open Order13DiamondQuotientConic Order13DiamondSexticSymmetry
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

def u : actualCurveFunctionField ℚ := quotientU (xImage ℚ)
def v : actualCurveFunctionField ℚ := quotientV (xImage ℚ) (yImage ℚ)

theorem u_fixed : diamondFieldMap u = u := by
  change diamondFieldMap (quotientU (xImage ℚ)) = quotientU (xImage ℚ)
  simp only [quotientU, map_div₀, map_sub, map_pow, map_mul, map_add,
    map_ofNat, map_one, diamondFieldMap_x]
  exact quotientU_diamond (xImage ℚ) xImage_ne_zero xImage_add_one_ne_zero

theorem v_negated : diamondFieldMap v = -v := by
  change diamondFieldMap (quotientV (xImage ℚ) (yImage ℚ)) = -quotientV (xImage ℚ) (yImage ℚ)
  simp only [quotientV, map_div₀, map_mul, map_add, map_one,
    diamondFieldMap_x, diamondFieldMap_y]
  exact quotientV_diamond (xImage ℚ) (yImage ℚ) xImage_ne_zero xImage_add_one_ne_zero

theorem square_fixes_u : diamondSecond u = u := by
  change diamondFieldMap (diamondFieldMap u) = u
  rw [u_fixed, u_fixed]

theorem square_fixes_v : diamondSecond v = v := by
  change diamondFieldMap (diamondFieldMap v) = v
  rw [v_negated, map_neg, v_negated, neg_neg]

theorem conic_equation : v ^ 2 = u ^ 2 + 2 * u + 5 :=
  quotient_conic (xImage ℚ) (yImage ℚ) xImage_ne_zero xImage_add_one_ne_zero yImage_sq

theorem cubic_equation : fiberCubic u (xImage ℚ) = 0 :=
  fiberCubic_quotientU (xImage ℚ) xImage_ne_zero xImage_add_one_ne_zero

theorem cubic_orbit_norm (z : actualCurveFunctionField ℚ) :
    (z - xImage ℚ) * (z - diamondFieldMap (xImage ℚ)) *
      (z - diamondSecond (xImage ℚ)) = fiberCubic u z := by
  rw [diamondFieldMap_x]
  change (z - xImage ℚ) * (z - diamondX (xImage ℚ)) *
    (z - diamondFieldMap (diamondFieldMap (xImage ℚ))) = fiberCubic u z
  rw [diamondFieldMap_x, map_diamondX, diamondFieldMap_x]
  exact orbit_norm (xImage ℚ) z xImage_ne_zero xImage_add_one_ne_zero

end MazurTransfer.Order13ActualDiamondQuotientFunctions
#print axioms MazurTransfer.Order13ActualDiamondQuotientFunctions.conic_equation
#print axioms MazurTransfer.Order13ActualDiamondQuotientFunctions.cubic_orbit_norm


