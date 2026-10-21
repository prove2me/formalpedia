-- Prove2me | Definitions.Def_MazurTransfer_OriginalIntegralArithmeticFieldPointComparisonData20261020
-- name    : MazurTransfer_OriginalIntegralArithmeticFieldPointComparisonData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T02:56:34.751052+00:00
-- url     : https://prove2.me/theorems/c549d1da-1189-4c07-be37-bcb6951fcace
-- title:
--   Original integral arithmetic field point equivalence
-- statement:
--   Retain the original base-map equality and the same field-point equivalence, with the original actual Picard group provider. Complete original types and whole values of the constructor, chosen group structure and coefficient contexts are independently checked. Separate theorem interfaces give operation and arithmetic action compatibility. Named downstream consumer: actual integral norm-kernel Hopf arithmetic point labels.
-- source:
--   MazurTheorem Order13IntegralArithmeticFieldPointComparison by Vas and contributors; complete original field-point comparison types and whole values, preserving Apache-2.0 attribution.

import Definitions.Def_MazurTransfer_OriginalIntegralGenericPointComparisonData20261020
import Definitions.Def_MazurTransfer_OriginalRelativePointBaseCastData20261020
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricFieldPointsData
import Definitions.Def_MazurTransfer_FieldPointActionsAndNormPreimageDifferenceData
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: specialize the SAME canonical local/generic point
comparison to field-valued arithmetic points with the canonical scalar
tower. Preserve actual multiplication, zero, norm maps and the existing
arithmetic Galois action by spectrum precomposition.
Named downstream consumer: actual integral norm-kernel Hopf point labels.
-/

noncomputable section
namespace MazurTransfer.Order13IntegralArithmeticFieldPointComparison
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13IntegralGenericPointComparison RelativePointBaseCast
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardGeometricNormPreimages
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
variable (K : Type) [Field K] [CharZero K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralArithmeticFieldPointComparison : GrpObj (Over.mk actualPicard.toBase) := actualGroup

theorem fieldBase_comp :
    FieldAutomorphismOverPointAction.fieldBase ℚ K ≫ localGenericInclusion q =
      FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℚ K)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (LocalRing q) ℚ)) =
      Spec.map (CommRingCat.ofHom (algebraMap (LocalRing q) K))
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (IsScalarTower.algebraMap_apply (LocalRing q) ℚ K r).symm

def actualFieldPointEquiv : Points K ≃
    SchemeHomOver (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)
      (localPicard q hq).toBase :=
  (actualLocalPointEquiv q hq (FieldAutomorphismOverPointAction.fieldBase ℚ K)).trans
    (pointEquiv (fieldBase_comp q K))











end MazurTransfer.Order13IntegralArithmeticFieldPointComparison
#print axioms MazurTransfer.Order13IntegralArithmeticFieldPointComparison.fieldBase_comp
#print axioms MazurTransfer.Order13IntegralArithmeticFieldPointComparison.actualFieldPointEquiv
#print axioms MazurTransfer.Order13IntegralArithmeticFieldPointComparison.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralArithmeticFieldPointComparison


