-- Prove2me | Definitions.Def_MazurTransfer_OriginalActualIntegralNormPreimageTorsorsData20261020
-- name    : MazurTransfer_OriginalActualIntegralNormPreimageTorsorsData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-11-02T17:07:47.002207+00:00
-- url     : https://prove2.me/theorems/3b15891c-35ad-4cab-b5e6-ded130450f7a
-- title:
--   Original actual integral norm preimage torsor predicate
-- statement:
--   Apply the checked finite flat preimage torsor theorem to both same actual integral norm extensions at every original good prime and every given local Picard section. Their checked finiteness, flatness, local finite presentation, surjectivity and all-scheme-point unit and multiplication identities supply the exact original hypotheses. Retain the original preimage fibre and its principal-action isomorphism on every test scheme. The complete original proposition and helper type, original torsor predicate type and whole value, three scoped provider types and one group-provider whole value, both private original-type preservation certificates, all generated helper types and every original torsor and coefficient context are independently checked. Named downstream consumer: the selected literal mu19 pi quotient torsor and its Kummer unit condition.
-- source:
--   MazurTheorem Order13ActualIntegralNormPreimageTorsors by Vas and contributors; same selected pi quotient and normalized literal mu19 model, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalActualPiMu19CoherentQuotientData20261020
import Definitions.Def_MazurTransfer_OriginalRelativeFiniteFlatNormPreimageTorsorData20261020
import Theorems.Thm_MazurTransfer_original_integral_norm_unit_and_all_point_identities
import Theorems.Thm_MazurTransfer_original_integral_norm_multiplication
noncomputable section

namespace MazurTransfer.Order13GoodPrimeIntegralNormPointwiseUnit
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup
private theorem integralNorm_preserves_all_units (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
 (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
 {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (LocalRing q))) :
 NeronModelInfra.schemeHomOverComp ((localLaw q hq).one t) (integralNorm q hq φ) = (localLaw q hq).one t :=
 MazurTransfer.original_integral_norm_unit_and_all_point_identities.2.2 q hq φ t
end MazurTransfer.Order13GoodPrimeIntegralNormPointwiseUnit
namespace MazurTransfer.Order13GoodPrimeIntegralNormGroupLaws
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup
private theorem integralNorm_preserves_mul (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
 (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
 {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (LocalRing q))) (x y : SchemeHomOver t (localPicard q hq).toBase) :
 NeronModelInfra.schemeHomOverComp ((localLaw q hq).mul t x y) (integralNorm q hq φ) =
 (localLaw q hq).mul t (NeronModelInfra.schemeHomOverComp x (integralNorm q hq φ))
 (NeronModelInfra.schemeHomOverComp y (integralNorm q hq φ)) :=
 MazurTransfer.original_integral_norm_multiplication q hq φ t x y
end MazurTransfer.Order13GoodPrimeIntegralNormGroupLaws
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: BOTH SAME actual integral norm extensions have actual
finite-flat fppf preimage torsors of EVERY given local Picard section.
Retain the principal-action isomorphism on ALL scheme-valued points.
Named downstream consumer: the selected normalized mu19 pi quotient's
unit Kummer condition at nineteen, and inverse-character twisted descent.
-/

noncomputable section
namespace MazurTransfer.Order13ActualIntegralNormPreimageTorsors
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeIntegralNormGroupLaws
open Order13GoodPrimeIntegralNormPointwiseUnit
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open RelativeFiniteFlatNormPreimageTorsor
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralNormPreimageTorsors : GrpObj (Over.mk actualPicard.toBase) := actualGroup
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
variable (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of (LocalRing q)))) (localPicard q hq).toBase)

def HasIntegralNormPreimageTorsor : Prop :=
  HasFiniteFlatPreimageTorsor (localLaw q hq) (integralNorm q hq φ)
    (fun t => integralNorm_preserves_all_units q hq φ t)
    (fun t x y => integralNorm_preserves_mul q hq φ t x y) a

local instance instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualIntegralNormPreimageTorsors : IsMonHom schemePi := schemePi_isMonHom
local instance instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualIntegralNormPreimageTorsors : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom



end MazurTransfer.Order13ActualIntegralNormPreimageTorsors

#print axioms MazurTransfer.Order13ActualIntegralNormPreimageTorsors.HasIntegralNormPreimageTorsor
#print axioms MazurTransfer.Order13ActualIntegralNormPreimageTorsors.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualIntegralNormPreimageTorsors
#print axioms MazurTransfer.Order13ActualIntegralNormPreimageTorsors.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualIntegralNormPreimageTorsors
#print axioms MazurTransfer.Order13ActualIntegralNormPreimageTorsors.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralNormPreimageTorsors


