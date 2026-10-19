-- Prove2me | Definitions.Def_MazurTransfer_Order13ArithmeticPicardOverHomPointMapsOriginalData20261018
-- name    : MazurTransfer_Order13ArithmeticPicardOverHomPointMapsOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T16:58:08.536492+00:00
-- url     : https://prove2.me/theorems/927ffd15-9f21-4eb9-9b6b-7f33119dd65c
-- title:
--   Original arithmetic Picard maps between points and Over-category morphisms
-- statement:
--   Retain the original maps from Over-category rational morphisms to scheme points, their inverse, and the arithmetic divisor-class map on such morphisms. All three complete original declaration types and all three nonproof values are checked. The named downstream consumer is the original rational Picard class-group equivalence, transporting the actual rational norm kernels. This interface asserts no kernel cardinality or rank.
-- source:
--   MazurTheorem Order13ActualArithmeticPicardPointMapGroup: original pointOfOverHom, overHomOfPoint, arithmeticClassOver; official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT Picard and divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: retain the exact maps between scheme points and Over-category morphisms, and the arithmetic class map on these morphisms. Named downstream consumer: rationalClassEquiv in Order13ActualPicardRationalNormComparison, transporting the actual rational norm kernels.
-/
import Definitions.Def_MazurTransfer_Order13ArithmeticPicardPointMapData
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
namespace MazurTransfer.Order13ArithmeticPicardPointMap
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)

noncomputable def pointOfOverHom (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase :=
  ⟨a.left, by simpa only [Over.mk_left, Over.mk_hom] using Over.w a⟩

noncomputable def overHomOfPoint (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :
    Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase :=
  Over.homMk a.1 a.2

noncomputable def arithmeticClassOver
    (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase) :
    Pic0 K (actualCurveFunctionField K) :=
  arithmeticClass K 𝒱 ε D h (pointOfOverHom K D a)


end MazurTransfer.Order13ArithmeticPicardPointMap
#print axioms MazurTransfer.Order13ArithmeticPicardPointMap.pointOfOverHom
#print axioms MazurTransfer.Order13ArithmeticPicardPointMap.overHomOfPoint
#print axioms MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClassOver


