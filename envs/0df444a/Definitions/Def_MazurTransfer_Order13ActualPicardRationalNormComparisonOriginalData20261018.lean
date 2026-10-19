-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardRationalNormComparisonOriginalData20261018
-- name    : MazurTransfer_Order13ActualPicardRationalNormComparisonOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T18:14:08.785915+00:00
-- url     : https://prove2.me/theorems/40fa153d-3331-45f2-a84d-2d88cdd1e2e8
-- title:
--   Original rational Picard class equivalence and norm point maps
-- statement:
--   Retain the original rational-point type, arithmetic Picard group, class equivalence from rational represented-Picard points to arithmetic divisor classes, and the two rational norm point maps for the actual X₁(13) curve. All five complete constructor types and all five nonproof values are checked against the originals. The four group providers and two field-context providers are also compared, including both nonproof values. Named downstream consumers are the two kernel equivalences used to transport arithmetic norm-kernel cardinalities to rational Picard points.
-- source:
--   MazurTheorem Order13ActualPicardRationalNormComparison: RationalPoints, ArithmeticPicard, rationalClassEquiv, rationalPi, rationalPiConjugate; official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_PublicArithmeticPicardGroupEquivOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePi_isMonHom
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePiConjugate_isMonHom
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT Picard and divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the original rational arithmetic class equivalence and the two norm maps on the same represented Picard rational points. Named downstream consumer: rationalPiKernelEquiv and rationalPiConjugateKernelEquiv in Order13ActualPicardRationalNormKernelCardinality.
-/
noncomputable section
namespace MazurTransfer.Order13ActualPicardRationalNormComparison
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardGeometricDiamondGroupAction Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardSchemeNormGroupHom
open scoped CategoryTheory.MonObj
local instance rationalNormComparisonOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance rationalNormComparisonOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local instance rationalNormComparisonOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
local instance rationalNormComparisonOriginalCommProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj
local instance rationalNormComparisonOriginalPiHomProvider20261018 : IsMonHom schemePi := schemePi_isMonHom
local instance rationalNormComparisonOriginalConjugateHomProvider20261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

abbrev RationalPoints := Over.mk (𝟙 (Spec (CommRingCat.of ℚ))) ⟶ Over.mk actualPicard.toBase
abbrev ArithmeticPicard := Order13ActualDiamondPicardEndomorphisms.ActualPicard
variable (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)

def rationalClassEquiv : RationalPoints ≃* Multiplicative ArithmeticPicard :=
  PublicArithmeticPicardGroupEquiv.arithmeticClassGroupEquiv ℚ 𝒱 infinitySection
    actualPicard actualRepresentation

def rationalPi : RationalPoints →* RationalPoints where
  toFun a := a ≫ schemePi
  map_one' := MonObj.one_comp schemePi
  map_mul' a b := MonObj.mul_comp a b schemePi

def rationalPiConjugate : RationalPoints →* RationalPoints where
  toFun a := a ≫ schemePiConjugate
  map_one' := MonObj.one_comp schemePiConjugate
  map_mul' a b := MonObj.mul_comp a b schemePiConjugate

end MazurTransfer.Order13ActualPicardRationalNormComparison
#print axioms MazurTransfer.Order13ActualPicardRationalNormComparison.rationalNormComparisonOriginalFactProvider20261018
#print axioms MazurTransfer.Order13ActualPicardRationalNormComparison.rationalNormComparisonOriginalAlgebraProvider20261018
#print axioms MazurTransfer.Order13ActualPicardRationalNormComparison.rationalNormComparisonOriginalGroupProvider20261018
#print axioms MazurTransfer.Order13ActualPicardRationalNormComparison.rationalNormComparisonOriginalCommProvider20261018
#print axioms MazurTransfer.Order13ActualPicardRationalNormComparison.rationalNormComparisonOriginalPiHomProvider20261018
#print axioms MazurTransfer.Order13ActualPicardRationalNormComparison.rationalNormComparisonOriginalConjugateHomProvider20261018
#print axioms MazurTransfer.Order13ActualPicardRationalNormComparison.RationalPoints
#print axioms MazurTransfer.Order13ActualPicardRationalNormComparison.ArithmeticPicard
#print axioms MazurTransfer.Order13ActualPicardRationalNormComparison.rationalClassEquiv
#print axioms MazurTransfer.Order13ActualPicardRationalNormComparison.rationalPi
#print axioms MazurTransfer.Order13ActualPicardRationalNormComparison.rationalPiConjugate


