-- Prove2me | Definitions.Def_MazurTransfer_OriginalNineteenIntegralPointCompatibilityData20261020
-- name    : MazurTransfer_OriginalNineteenIntegralPointCompatibilityData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-11-02T17:28:12.793034+00:00
-- url     : https://prove2.me/theorems/77069596-1ef2-4577-b478-fccdcff59364
-- title:
--   Original chosen integral Picard point and fixed arithmetic field comparison
-- statement:
--   Retain the original chosen unique integral extension of the same rational Picard point. Its original uniqueness and restriction properties imply the original generic projection equality. Compatibility of field base maps then identifies its field points with the previously fixed arithmetic field-point comparison over every original characteristic-zero field and scalar tower. All four complete original propositions and helper types, both original constructor full types and whole values, both scoped provider types and the group-provider whole value, the original-type private unique-extension certificate, all generated helper types and all original coefficient and arithmetic point contexts are independently checked. Named downstream consumer: both actual norm-preimage torsors and the original selected character Kummer cocycle.
-- source:
--   MazurTheorem Order13NineteenIntegralPointCompatibility by Vas and contributors; same selected pi quotient and normalized literal mu19 model, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalActualIntegralNormPreimageTorsorsData20261020
import Definitions.Def_MazurTransfer_OriginalExceptionalNineteenNormModelData20261020
import Theorems.Thm_MazurTransfer_original_exceptional_nineteen_norm_model_properties
noncomputable section

namespace MazurTransfer.Order13ExceptionalNineteenFlatNormFibres
open CategoryTheory AlgebraicGeometry NeronModelInfra
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
attribute [local instance] MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.instFactPrimeOfNatNat_order13ExceptionalNineteenFlatNormFibres
private theorem actual_generic_point_has_unique_integral_extension
 (z : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase) :
 ∃! x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (LocalRing 19)))) integralModel.toBase,
 genericFibreRestrict (LocalRing 19) ℚ integralModel.toBase
 (𝟙 (Spec (CommRingCat.of (LocalRing 19)))) x = actualGenericPoint z :=
 MazurTransfer.original_exceptional_nineteen_norm_model_properties.2.1 z
end MazurTransfer.Order13ExceptionalNineteenFlatNormFibres
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the UNIQUE integral extension of the SAME actual rational
Picard point agrees with the PREVIOUSLY FIXED arithmetic field comparison
at every compatible characteristic-zero field. Both norm torsors use it.
Named downstream consumer: identification of the actual norm-preimage
torsor's field points and its original selected character Kummer cocycle.
-/

noncomputable section
namespace MazurTransfer.Order13NineteenIntegralPointCompatibility
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13ExceptionalNineteenFlatNormFibres Order13LocalIntegralCoefficientMaps
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeLocalGenericPicardComparison
open Order13IntegralGenericPointComparison Order13IntegralArithmeticFieldPointComparison
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricNormPreimages
open RelativeNormPreimageRepresentation Order13ActualIntegralNormPreimageTorsors
open scoped CategoryTheory.MonObj
local instance instFactPrimeOfNatNat_order13NineteenIntegralPointCompatibility : Fact (Nat.Prime 19) := ⟨by norm_num⟩
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13NineteenIntegralPointCompatibility : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local notation "R" => LocalRing 19

variable (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase)

def integralPoint : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) integralModel.toBase :=
  (actual_generic_point_has_unique_integral_extension a).choose







variable (K : Type) [Field K] [CharZero K]
variable [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K]

def fixedActualFieldPointEquiv :=
  @Order13IntegralArithmeticFieldPointComparison.actualFieldPointEquiv 19 inferInstance nineteen_good
    K _ _ aRK tRQ



end MazurTransfer.Order13NineteenIntegralPointCompatibility

#print axioms MazurTransfer.Order13NineteenIntegralPointCompatibility.integralPoint
#print axioms MazurTransfer.Order13NineteenIntegralPointCompatibility.fixedActualFieldPointEquiv
#print axioms MazurTransfer.Order13NineteenIntegralPointCompatibility.instFactPrimeOfNatNat_order13NineteenIntegralPointCompatibility
#print axioms MazurTransfer.Order13NineteenIntegralPointCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13NineteenIntegralPointCompatibility


