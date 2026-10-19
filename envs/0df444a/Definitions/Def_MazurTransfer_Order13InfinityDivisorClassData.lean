-- Prove2me | Definitions.Def_MazurTransfer_Order13InfinityDivisorClassData
-- name    : MazurTransfer_Order13InfinityDivisorClassData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T13:37:47.281403+00:00
-- url     : https://prove2.me/theorems/40c01e47-bb12-43b6-b822-f1d42ed9b62f
-- title:
--   The degree-zero divisor difference of the actual infinity places and its arithmetic Picard class
-- statement:
--   For the two literal rational infinity places $v_+,v_-$ of the order-13 curve, the specified degree-zero divisor and its arithmetic Picard class are $$\Delta=[v_-]-[v_+],\qquad c=[\Delta]\in\operatorname{Pic}^0(C/\mathbb Q).$$ The constructors use the original degree-one certificates. They supply the exact-order nineteen result.
-- source:
--   Original complete infinityDifferenceDivisor and infinityClass declarations and bodies from MazurTheorem Order13InfinityPicardClassOrder.lean, Apache-2.0, Vas and contributors. Two full original types and two data values are kernel-compared. Public original infinity and Pell divisor data supply dependencies. Named downstream consumer: the actual infinity class has exact additive order nineteen.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the explicit principal divisor makes the nonzero difference
of the actual infinity section classes an element of exact order nineteen.
Named downstream consumer: the lower bound matching the rational arithmetic
Picard torsion bound from the two good reductions.
-/
import Definitions.Def_MazurTransfer_Order13PellPrincipalDivisorData
noncomputable section
namespace MazurTransfer.Order13InfinityPicardClassOrder
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13IntegralSections Order13RationalSectionPicardInjection
open Order13PellPrincipalDivisor Order13ActualInfinityPlaceCenters
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

def infinityDifferenceDivisor : Divisor.degZero (K := ℚ) (F := actualCurveFunctionField ℚ) :=
  ⟨Finsupp.single negativePlace 1 - Finsupp.single positivePlace 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single]
    have Hn := infinityPlace_deg (-1) (Order13PellInfinityLocalOrders.negativeProof ℚ)
    have Hp := infinityPlace_deg 1 (Order13PellInfinityLocalOrders.positiveProof ℚ)
    rw [infinityPlace_eq_actualPlaceOfPoint] at Hn Hp
    change negativePlace.deg = 1 at Hn
    change positivePlace.deg = 1 at Hp
    rw [Hn, Hp]
    norm_num⟩

def infinityClass : Pic0 ℚ (actualCurveFunctionField ℚ) := Pic0.mk infinityDifferenceDivisor

end MazurTransfer.Order13InfinityPicardClassOrder
#print axioms MazurTransfer.Order13InfinityPicardClassOrder.infinityDifferenceDivisor
#print axioms MazurTransfer.Order13InfinityPicardClassOrder.infinityClass


