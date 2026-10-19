-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardDiamondSchemeEndomorphism
-- name    : MazurTransfer_Order13ActualPicardDiamondSchemeEndomorphism
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:36:32.385993+00:00
-- url     : https://prove2.me/theorems/60efc101-82b6-4f02-828e-077117935aec
-- title:
--   The genuine diamond endomorphism of the actual rational Picard scheme
-- statement:
--   The inverse of the actual diamond curve isomorphism acts on the actual represented rational Picard scheme by re-rigidified pullback. This gives a scheme endomorphism $\Delta:J\to J$ which acts naturally on every test scheme and preserves the relative group law: $$\Delta(xy)=\Delta(x)\Delta(y),\qquad\Delta(1)=1.$$ The same construction is supplied for every representing designation. It is the concrete scheme action used in the nineteen norm relation and rational rank descent.
-- source:
--   Original complete six constructors and group-compatibility certificates from MazurTheorem Order13ActualPicardDiamondSchemeEndomorphism.lean, Apache-2.0, Vas and contributors. Six complete original closed types and four data values are kernel-compared. The already-public rational Picard designation supplies the three original preliminary constructors. All remaining bodies are unchanged. Named downstream consumer: arithmetic diamond comparison and actual Picard norm relation.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual diamond inverse acts by re-rigidified pullback
on every represented Picard scheme of the literal order-13 curve over Q.
The construction acts on all test schemes and respects multiplication and
identity. Named downstream consumer: comparison with the arithmetic Picard
diamond and a genuine scheme version of the nineteen norm relation.
-/
import Definitions.Def_MazurTransfer_Order13ActualDiamondCurveAutomorphism
import Definitions.Def_MazurTransfer_Order13ActualRationalPicardDesignation
import Definitions.Def_MazurTransfer_PicardReRigidifiedCurvePullbackData
import Theorems.Thm_MazurTransfer_PicardReRigidifiedCurvePullback_nonempty_pullbackData

noncomputable section
namespace MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualDiamondCurveAutomorphism PicardReRigidifiedCurvePullback







def diamondAction {D : RelativePic0Designation ℚ (curveToBase ℚ)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) (curveToBase ℚ)}
    (h : RepresentsRelSubPic (curveToBase ℚ) ε (algEquivZeroCut (curveToBase ℚ) ε) D) :
    PullbackData h diamondCurveIso.inv diamondCurveIso_inv_over :=
  (nonempty_pullbackData h diamondCurveIso.inv diamondCurveIso_inv_over).some

def actualDiamondAction :
    PullbackData actualRepresentation diamondCurveIso.inv diamondCurveIso_inv_over :=
  diamondAction actualRepresentation

def actualLaw := RepresentsRelSubPic.relativeGroupLaw
  (P := algEquivZeroGroupCut (curveToBase ℚ) infinitySection) actualRepresentation

def actualDiamondHom : SchemeHomOver actualPicard.toBase actualPicard.toBase :=
  actualDiamondAction.hom

theorem actualDiamondHom_mul {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (x y : SchemeHomOver t actualPicard.toBase) :
    postComp actualDiamondHom (actualLaw.mul t x y) =
      actualLaw.mul t
        (postComp actualDiamondHom x) (postComp actualDiamondHom y) :=
  actualDiamondAction.mul t x y

theorem actualDiamondHom_one {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ)) :
    postComp actualDiamondHom (actualLaw.one t) =
      actualLaw.one t :=
  actualDiamondAction.one t

end MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
#print axioms MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism.actualRepresentation
#print axioms MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism.actualDiamondAction
#print axioms MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism.actualDiamondHom_mul
#print axioms MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism.actualDiamondHom_one


