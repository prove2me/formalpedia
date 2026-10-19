-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldMap
-- name    : MazurTransfer_Order13ActualDiamondFunctionFieldMap
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:20:02.445785+00:00
-- url     : https://prove2.me/theorems/8852ecc5-452a-406e-90dc-5f65377f77b4
-- title:
--   The actual diamond endomorphism of the rational function field
-- statement:
--   For the literal order-thirteen curve over $\mathbb Q$, the actual injective ordinary diamond coordinate map extends to an endomorphism of its existing scheme function field. Its coordinate formulas are $$x\longmapsto-\frac1{x+1},\qquad y\longmapsto\frac{y}{(x+1)^3}.$$ The extension agrees with the original coordinate homomorphism on the entire ordinary coordinate algebra. This is the concrete endomorphism used to construct the diamond field automorphism.
-- source:
--   Original complete four declarations from MazurTheorem Order13ActualDiamondFunctionFieldMap.lean, Apache-2.0, Vas and contributors. Four complete original closed types and the actual field-map value are kernel-compared. Public imports replace dependencies; no body is altered. Named downstream consumer: actual diamond field automorphism.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: extend the actual injective diamond coordinate map to
its specified endomorphism of the existing rational scheme function field.
Named downstream consumer: the actual diamond field automorphism. -/
import Definitions.Def_MazurTransfer_Order13ActualOrdinaryDiamondCoordinateMap
import Theorems.Thm_MazurTransfer_Order13ActualDiamondFunctionFieldMap_ordinaryDiamond_injective
noncomputable section
namespace MazurTransfer.Order13ActualDiamondFunctionFieldMap
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13DiamondSexticSymmetry Order13ActualOrdinaryPolynomialTranscendence
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
def diamondFieldMap : actualCurveFunctionField ℚ →+* actualCurveFunctionField ℚ :=
  IsFractionRing.lift ordinaryDiamond_injective

theorem diamondFieldMap_coordinate (b : CoordinateRing ℚ) :
    diamondFieldMap (algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ) b) = ordinaryDiamond b :=
  IsFractionRing.lift_algebraMap ordinaryDiamond_injective b

theorem diamondFieldMap_x : diamondFieldMap (xImage ℚ) = diamondX (xImage ℚ) :=
  (diamondFieldMap_coordinate (xCoordinate ℚ)).trans ordinaryDiamond_x

theorem diamondFieldMap_y : diamondFieldMap (yImage ℚ) = diamondY (xImage ℚ) (yImage ℚ) :=
  (diamondFieldMap_coordinate (yCoordinate ℚ)).trans ordinaryDiamond_y
end MazurTransfer.Order13ActualDiamondFunctionFieldMap
#print axioms MazurTransfer.Order13ActualDiamondFunctionFieldMap.diamondFieldMap


