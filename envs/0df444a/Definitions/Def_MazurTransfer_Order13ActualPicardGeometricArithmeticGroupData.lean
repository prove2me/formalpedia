-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticGroupData
-- name    : MazurTransfer_Order13ActualPicardGeometricArithmeticGroupData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T19:37:12.315231+00:00
-- url     : https://prove2.me/theorems/5efc115c-b2b6-4afa-9fcb-6c95e1b16707
-- title:
--   Original over-category geometric Picard points and their actual arithmetic classes
-- statement:
--   For a perfect characteristic-zero field K, retain the original conversions between K-valued points of the same existing rational represented Picard family and morphisms in the over category above Spec Q. On the actual curve over K, define the arithmetic class of such an over-category point by the original degree-zero divisor class of its associated geometric line bundle. The complete original types and all three constructor values are preserved, as is the original scalar algebra provider. The named downstream consumer is the geometric arithmetic group law and injectivity needed to transport diamond norms to the same Picard scheme.
-- source:
--   Original MazurTheorem Order13ActualPicardGeometricArithmeticGroup.pointOfOverHom, overHomOfPoint and geometricArithmeticClassOver constructors, all unchanged. Official Anthropic FLT relative Picard inputs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify field points in the over category with the original
represented Picard field points and retain the original arithmetic class.
Named downstream consumer: the geometric arithmetic group law and point
injectivity for the same rational order-13 Picard scheme. Original
MazurTheorem Order13ActualPicardGeometricArithmeticGroup constructors.
Official Anthropic FLT inputs: 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticClassDataExplicitPublicConstructors20261017
noncomputable section
namespace MazurTransfer.Order13ActualPicardGeometricArithmeticGroup
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGeometricArithmeticClass
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
noncomputable def pointOfOverHom (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase :=
  ⟨a.left, by simpa only [Over.mk_left, Over.mk_hom] using Over.w a⟩

noncomputable def overHomOfPoint (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase :=
  Over.homMk a.1 a.2

noncomputable def geometricArithmeticClassOver
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase) :
    Pic0 K (actualCurveFunctionField K) :=
  geometricArithmeticClass K 𝒱 (pointOfOverHom K a)


end MazurTransfer.Order13ActualPicardGeometricArithmeticGroup
#print axioms MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.pointOfOverHom
#print axioms MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.overHomOfPoint
#print axioms MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver


