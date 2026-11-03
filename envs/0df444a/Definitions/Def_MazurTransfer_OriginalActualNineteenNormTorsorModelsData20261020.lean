-- Prove2me | Definitions.Def_MazurTransfer_OriginalActualNineteenNormTorsorModelsData20261020
-- name    : MazurTransfer_OriginalActualNineteenNormTorsorModelsData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-11-02T19:13:13.667433+00:00
-- url     : https://prove2.me/theorems/a3e5dcad-ce78-4eba-b112-fdc9efa7bf79
-- title:
--   Original both canonical actual nineteen norm torsor predicate
-- statement:
--   Specialize the checked original two integral norm preimage torsors at nineteen to the same canonical chosen unique extension of each original rational Picard point. Retain its checked restriction and uniqueness, both actual norm morphisms, the original principal action on all scheme points, and the same coherent selected pi quotient in normalized literal mu19 coordinates. Both complete original propositions and helper types, the entire original canonical-model predicate type and whole value, all four scoped provider types and one group-provider value, all generated helper types and original model and point contexts are independently checked. No local unit condition is asserted. Named downstream consumer: actual literal mu19 torsor-cocycle pushforward and the nineteen Kummer unit condition.
-- source:
--   MazurTheorem Order13ActualNineteenNormTorsorModels by Vas and contributors; both canonical norm fibres and the same normalized selected pi model, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalNineteenIntegralPointCompatibilityData20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: BOTH actual nineteen norm torsors use the SAME canonical
unique integral extension of EACH previously defined rational Picard point.
Retain the coherent normalized selected-pi kernel quotient alongside them.
Named downstream consumer: actual mu19 torsor-cocycle pushforward and the
nineteen unit Kummer condition; a unit condition is not asserted here.
-/

noncomputable section
namespace MazurTransfer.Order13ActualNineteenNormTorsorModels
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13LocalIntegralCoefficientMaps Order13ExceptionalNineteenFlatNormFibres
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardNormKummerCocycles Order13NineteenIntegralPointCompatibility
open Order13ActualIntegralNormPreimageTorsors Order13ActualPiMu19CoherentQuotient
open MazurTorsion.XOneThirteenProjectiveCurve
open scoped CategoryTheory.MonObj
local instance instFactPrimeOfNatNat_order13ActualNineteenNormTorsorModels : Fact (Nat.Prime 19) := ⟨by norm_num⟩
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNineteenNormTorsorModels : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualNineteenNormTorsorModels : IsMonHom schemePi := schemePi_isMonHom
local instance instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualNineteenNormTorsorModels : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom
local notation "R" => LocalRing 19
local notation "F" => AlgebraicClosure ℚ

variable (a : RationalPoints)

def HasCanonicalActualNineteenNormTorsors : Prop :=
  genericFibreRestrict R ℚ integralModel.toBase (𝟙 (Spec (CommRingCat.of R)))
      (integralPoint (overHomToSchemeHomOver a)) = actualGenericPoint (overHomToSchemeHomOver a) ∧
  (∀ b : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) integralModel.toBase,
    genericFibreRestrict R ℚ integralModel.toBase (𝟙 (Spec (CommRingCat.of R))) b =
      actualGenericPoint (overHomToSchemeHomOver a) → b = integralPoint (overHomToSchemeHomOver a)) ∧
  HasIntegralNormPreimageTorsor 19 nineteen_good schemePi (integralPoint (overHomToSchemeHomOver a)) ∧
  HasIntegralNormPreimageTorsor 19 nineteen_good schemePiConjugate (integralPoint (overHomToSchemeHomOver a))





end MazurTransfer.Order13ActualNineteenNormTorsorModels

#print axioms MazurTransfer.Order13ActualNineteenNormTorsorModels.HasCanonicalActualNineteenNormTorsors
#print axioms MazurTransfer.Order13ActualNineteenNormTorsorModels.instFactPrimeOfNatNat_order13ActualNineteenNormTorsorModels
#print axioms MazurTransfer.Order13ActualNineteenNormTorsorModels.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualNineteenNormTorsorModels
#print axioms MazurTransfer.Order13ActualNineteenNormTorsorModels.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualNineteenNormTorsorModels
#print axioms MazurTransfer.Order13ActualNineteenNormTorsorModels.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNineteenNormTorsorModels


