-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondLineBundleData
-- name    : MazurTransfer_Order13ActualPicardGeometricDiamondLineBundleData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:46:52.358999+00:00
-- url     : https://prove2.me/theorems/1ec9c626-9f22-4da1-99ff-7a4663d2526d
-- title:
--   The same rational Picard diamond acts on geometric point line bundles by the actual inverse diamond curve pullback
-- statement:
--   A field-valued point of the existing rational represented Picard gives the original actual line bundle on the literal extension-field curve. Postcomposing by the existing generic-compatible rational diamond Picard morphism pulls that line bundle back along the inverse of the actual generic diamond curve lift over the field. Both complete original types, the actual geometric line-bundle constructor value and both original local scalar algebra providers are compared. Named downstream consumer: geometric divisor presentations and arithmetic-class compatibility for genuine scheme norm transport.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGeometricDiamondLineBundle, using the same original rational Picard representation and field action, actual curve base change and inverse-diamond naturality. Official Anthropic FLT relative Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the existing generic-compatible rational Picard diamond
acts on every characteristic-zero field point by inverse diamond pullback
on the literal curve over that field. Named downstream consumer: degree-zero
divisor presentations and arithmetic transport for geometric Picard points.
-/
import Definitions.Def_MazurTransfer_Order13GeometricRelativeCurveChangeData
import Definitions.Def_MazurTransfer_Order13GeometricInverseDiamondCurveNaturalityData
import Definitions.Def_MazurTransfer_PicardCurvePullbackGeometricFieldLineBundleData
import Definitions.Def_MazurTransfer_Order13ActualPicardGenericFieldActionData
import Definitions.Def_MazurTransfer_Order13FieldPicardArithmeticPullbackNaturalityData

noncomputable section
namespace MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGenericFieldAction
open Order13GeometricRelativeCurveChange PicardCurvePullbackGeometricFieldLineBundle
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

def actualGeometricPointLineBundle
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    (curveScheme K).Modules :=
  geometricPointLineBundle (curveToBase ℚ) infinitySection actualPicard actualRepresentation
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (geometricCurveEmbedding K) a

theorem actualGenericDiamondHom_geometric_point_pullback
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    Nonempty (actualGeometricPointLineBundle K
        (postComp (actualFieldHom Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv) a) ≅
      (Scheme.Modules.pullback (Order13FieldDiamondGenericCurveOrder.genericDiamondCurveIso K).inv).obj
        (actualGeometricPointLineBundle K a)) := by
  have hQ := Order13ActualPicardArithmeticPullbackNaturality.inverse_over
    Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv
  have hK := Order13FieldPicardArithmeticPullbackNaturality.inverse_over K
    (Order13FieldDiamondFunctionFieldAutomorphism.diamondAlgEquiv K)
  have hcomm := Order13GeometricInverseDiamondCurveNaturality.existingDiamondCurve_inverse_baseChange K
  have hcomp := geometricCurveEmbedding_curveChange K
    Order13ActualDiamondGenericCurveOrder.genericDiamondCurveIso.inv hQ
    (Order13FieldDiamondGenericCurveOrder.genericDiamondCurveIso K).inv hK hcomm
  exact geometricPointLineBundle_postComp_iso_pullback (curveToBase ℚ)
    infinitySection actualPicard actualRepresentation
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (geometricCurveEmbedding K)
    Order13ActualDiamondGenericCurveOrder.genericDiamondCurveIso.inv hQ
    (actualFieldAction Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv)
    (Order13FieldDiamondGenericCurveOrder.genericDiamondCurveIso K).inv hcomp a

end MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
#print axioms MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle.actualGenericDiamondHom_geometric_point_pullback


