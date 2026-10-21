-- Prove2me | Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
-- name    : MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T02:15:32.0279+00:00
-- url     : https://prove2.me/theorems/ae48c760-2e37-49af-90d0-45c02bded232
-- title:
--   Original chosen Picard groups for the same canonical comparisons
-- statement:
--   Retain the original three chosen group-object structures on the same actual Picard, rational fibre and local generic fibre. All three complete original scoped provider types and whole values, twelve context types and twelve whole context values, and all generated structural certificates are independently checked. Group compatibility of the canonical maps is a separate theorem interface. Named downstream consumer: the actual local generic point equivalence and integral norm-kernel arithmetic comparison.
-- source:
--   MazurTheorem Order13PicardComparisonPublicGroupCompatibility by Vas and contributors; complete original chosen group types and whole values, preserving Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: apply the accepted public pointwise group-morphism
contract to canonical comparisons for the SAME actual rational Picard,
the selected integral family's rational fibre, and every good-prime local
generic fibre. Named downstream consumer: actual local norm extensions.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericPicardComparisonDataNativeABIV3


noncomputable section
namespace MazurTransfer.Order13PicardComparisonPublicGroupCompatibility
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13SameIntegralPicardRationalSchemeComparison
open Order13GoodPrimeLocalGenericPicardComparison
open PicardCanonicalRepresentationGroupIsomorphism
open scoped CategoryTheory.MonObj
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13PicardComparisonPublicGroupCompatibility : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance instGrpObjOverSchemeSpecOfRatMkToBaseRationalFibre_order13PicardComparisonPublicGroupCompatibility : GrpObj (Over.mk rationalFibre.toBase) := rationalFibreGroup



variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
local instance instGrpObjOverSchemeSpecOfRatMkToBaseLocalGenericPicard_order13PicardComparisonPublicGroupCompatibility : GrpObj (Over.mk (localGenericPicard q hq).toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition
      (localGenericPicard q hq) from localGenericRepresentation q hq).grpObj



end MazurTransfer.Order13PicardComparisonPublicGroupCompatibility
#print axioms MazurTransfer.Order13PicardComparisonPublicGroupCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseLocalGenericPicard_order13PicardComparisonPublicGroupCompatibility
#print axioms MazurTransfer.Order13PicardComparisonPublicGroupCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseRationalFibre_order13PicardComparisonPublicGroupCompatibility
#print axioms MazurTransfer.Order13PicardComparisonPublicGroupCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13PicardComparisonPublicGroupCompatibility


