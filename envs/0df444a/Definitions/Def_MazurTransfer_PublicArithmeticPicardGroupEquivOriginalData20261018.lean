-- Prove2me | Definitions.Def_MazurTransfer_PublicArithmeticPicardGroupEquivOriginalData20261018
-- name    : MazurTransfer_PublicArithmeticPicardGroupEquivOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T18:10:23.972193+00:00
-- url     : https://prove2.me/theorems/34670380-a932-4001-b503-227e760ecc1d
-- title:
--   The original arithmetic Picard group equivalence
-- statement:
--   For a perfect field in which 104 is nonzero, a two-affine-open cover of the actual X₁(13) curve, and a supplied pointed relative Picard representation, construct the original multiplicative equivalence from Over-category rational points to degree-zero arithmetic divisor classes. The map is the original arithmetic class map and the inverse is supplied by its proved bijectivity. Its complete original type and entire nonproof value are compared with the original constructor. The named downstream consumer is rationalClassEquiv, transporting the actual rational norm kernels.
-- source:
--   MazurTheorem Order13ActualArithmeticPicardGroupEquivWithPublicClosedPoints.arithmeticClassGroupEquiv; official Anthropic FLT Picard and divisor interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13ArithmeticPicardOverHomPointMapsOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClassOver_one
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClassOver_mul
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClassOver_injective
import Theorems.Thm_MazurTransfer_PublicArithmeticPicardGroupEquiv_arithmeticClassOver_surjective
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT Picard and divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the original multiplicative equivalence from represented Picard rational points to degree-zero arithmetic divisor classes, constructed from the exact original arithmetic class map. Named downstream consumer: rationalClassEquiv in Order13ActualPicardRationalNormComparison, transporting the actual rational norm kernels.
-/
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open scoped CategoryTheory.MonObj
namespace MazurTransfer.PublicArithmeticPicardGroupEquiv
open MazurTransfer.Order13ArithmeticPicardPointMap
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)

noncomputable def arithmeticClassGroupEquiv :
    letI := (show RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
    (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase) ≃*
      Multiplicative (Pic0 K (actualCurveFunctionField K)) := by
  letI := (show RepresentsRelSubPic (curveToBase K) ε
    (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
  let f : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase) →*
      Multiplicative (Pic0 K (actualCurveFunctionField K)) :=
    { toFun := fun a => Multiplicative.ofAdd (arithmeticClassOver K 𝒱 ε D h a)
      map_one' := arithmeticClassOver_one K 𝒱 ε D h
      map_mul' := arithmeticClassOver_mul K 𝒱 ε D h }
  exact MulEquiv.ofBijective f
    ⟨arithmeticClassOver_injective K 𝒱 ε D h, arithmeticClassOver_surjective K 𝒱 ε D h⟩

end MazurTransfer.PublicArithmeticPicardGroupEquiv
#print axioms MazurTransfer.PublicArithmeticPicardGroupEquiv.arithmeticClassGroupEquiv


