-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
-- name    : MazurTransfer_Order13ActualPicardSchemeNineteenNormData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T20:24:34.918672+00:00
-- url     : https://prove2.me/theorems/29af81bb-b222-48ba-b27d-466ee7ec2feb
-- title:
--   The two original actual rational Picard norm-nineteen endomorphism constructors
-- statement:
--   Let P be the same actual rational represented Picard scheme and let delta be its existing scheme diamond. Retain the original endomorphisms pi=3 id+2 delta and pi-bar=5 id-2 delta, using the commutative group law on the group of scheme morphisms to P. Both complete original constructor values and their full types, and the original group-object provider on P, are compared. The named downstream consumer is the proof that both composites equal multiplication by nineteen. The constructor package does not assert isogeny degrees or rational rank.
-- source:
--   Complete original MazurTheorem Order13ActualPicardSchemeNineteenNorm.schemePi and schemePiConjugate, retaining both original values and the same represented Picard group object. Uses the original actual scheme diamond with official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two explicit endomorphisms of the same rational Picard
scheme have both composites equal to scalar nineteen. This establishes
the actual scheme norm identity; isogeny properties and degrees remain
separate obligations. Named downstream consumer: nineteen-isogeny descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondGroupActionExplicitConstructorFacts20261017

noncomputable section
namespace MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
open scoped CategoryTheory.MonObj
local instance originalNormPicardGroupObject20261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

def schemePi : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase :=
  (𝟙 (Over.mk actualPicard.toBase)) ^ 3 * schemeDiamond ^ 2

def schemePiConjugate : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase :=
  (𝟙 (Over.mk actualPicard.toBase)) ^ 5 * (schemeDiamond ^ 2)⁻¹

end MazurTransfer.Order13ActualPicardSchemeNineteenNorm
#print axioms MazurTransfer.Order13ActualPicardSchemeNineteenNorm.schemePi
#print axioms MazurTransfer.Order13ActualPicardSchemeNineteenNorm.schemePiConjugate


