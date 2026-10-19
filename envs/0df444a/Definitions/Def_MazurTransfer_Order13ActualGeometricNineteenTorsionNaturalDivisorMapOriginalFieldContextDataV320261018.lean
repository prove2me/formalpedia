-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualGeometricNineteenTorsionNaturalDivisorMapOriginalFieldContextDataV320261018
-- name    : MazurTransfer_Order13ActualGeometricNineteenTorsionNaturalDivisorMapOriginalFieldContextDataV320261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T10:54:03.106823+00:00
-- url     : https://prove2.me/theorems/ea108a89-7e6d-4574-ab21-f30d91bfa560
-- title:
--   The original natural divisor-class map on actual Picard nineteen-torsion
-- statement:
--   This interface defines the original degree-zero arithmetic Picard carrier, the natural additive divisor-class map from actual rational Picard field points, and its restriction to nineteen-torsion. It preserves the original field and group constructors. It asserts neither injectivity nor surjectivity; those are subsequent proof contracts used for natural transport of the Weil pairing.
-- source:
--   MazurTheorem Order13ActualGeometricNineteenTorsionDivisorComparison.ArithmeticPicard, geometricClassAddHom and geometricTorsionClassHom; complete original types and nonproof values preserved, including original field contexts.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original constructors for the natural geometric
divisor-class map on actual nineteen-torsion. No bijectivity assertion
about the natural map is included.
Named downstream consumer: natural geometric nineteen-torsion divisor
comparison and transport of the actual divisorial pairing.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardAlgPointsComparisonData20261018
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondGroupActionExplicitConstructorFacts20261017
noncomputable section
namespace MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGeometricNormPreimages
open Order13ActualNormKernelProductCardinality Order13ActualPicardAlgPointsComparison
open Order13ActualPicardGeometricArithmeticGroup Order13ActualPicardGeometricDiamondGroupAction
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018
variable (K : Type) [Field K] [CharZero K]
local instance naturalDivisorMapOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance naturalDivisorMapOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

abbrev ArithmeticPicard := Pic0 K (actualCurveFunctionField K)
variable [IsAlgClosed K]

def geometricClassAddHom : Additive (Points K) →+ ArithmeticPicard K :=
  (geometricClassHom K
    (GoodCharacteristicGeometryPublicProof.MazurTorsion.XOneThirteenProjectiveCurve.actualTwoAffineOpenCover K)).toAdditiveLeft

def geometricTorsionClassHom :
    NineteenTorsion K →+ Pic0.torsion K (actualCurveFunctionField K) 19 where
  toFun x := ⟨geometricClassAddHom K x.val, by
    change (19 : ℤ) • geometricClassAddHom K x.val = 0
    have hx : (19 : ℕ) • x.val = 0 := x.property
    erw [natCast_zsmul, ← map_nsmul (geometricClassAddHom K), hx, map_zero]⟩
  map_zero' := Subtype.ext (map_zero (geometricClassAddHom K))
  map_add' x y := Subtype.ext (map_add (geometricClassAddHom K) x.val y.val)

end MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison
#print axioms MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison.geometricTorsionClassHom
#print axioms MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison.geometricClassAddHom


