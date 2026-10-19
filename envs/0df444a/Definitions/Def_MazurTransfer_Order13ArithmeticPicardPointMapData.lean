-- Prove2me | Definitions.Def_MazurTransfer_Order13ArithmeticPicardPointMapData
-- name    : MazurTransfer_Order13ArithmeticPicardPointMapData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T15:21:55.342986+00:00
-- url     : https://prove2.me/theorems/29e2bbbb-eb51-404c-92cf-1540ff101b99
-- title:
--   Actual Picard-point divisor and arithmetic class constructors
-- statement:
--   The unchanged original pointDivisor and arithmeticClass definitions attach the original chosen degree-zero divisor and its Pic0 class to any base-field represented Picard point of the literal order-13 curve. Both complete types and both data values are checked against the original source. Downstream consumer: arithmetic-class presentation independence and inverse pullback naturality.
-- source:
--   MazurTheorem original Order13ActualArithmeticPicardPointMap, Apache-2.0; official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original pointDivisor and arithmeticClass constructors preserved unchanged.
Design boundary: attach the original arithmetic Pic0 class to any represented
actual Picard point, with its complete chosen degree-zero divisor retained.
Named downstream consumer: arithmetic-class presentation independence and
actual Picard pullback naturality. Official Anthropic FLT interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Theorems.Thm_MazurTransfer_order13_actual_picard_point_degreeZero_divisor_presentation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.LineBundleFieldComparison

namespace MazurTransfer.Order13ArithmeticPicardPointMap

variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)
variable (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase)

noncomputable def pointDivisor : Divisor.degZero (K := K) (F := actualCurveFunctionField K) :=
  (MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h a).choose

noncomputable def arithmeticClass : Pic0 K (actualCurveFunctionField K) :=
  Pic0.mk (pointDivisor K 𝒱 ε D h a)

end MazurTransfer.Order13ArithmeticPicardPointMap

#print axioms MazurTransfer.Order13ArithmeticPicardPointMap.pointDivisor
#print axioms MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClass


