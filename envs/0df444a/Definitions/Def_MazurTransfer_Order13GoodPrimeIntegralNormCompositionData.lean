-- Prove2me | Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormCompositionData
-- name    : MazurTransfer_Order13GoodPrimeIntegralNormCompositionData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T04:35:52.691701+00:00
-- url     : https://prove2.me/theorems/25890ee5-0d25-4069-9a7c-74f9777962dd
-- title:
--   Composition and scalar-nineteen extension identities for the actual local norms
-- statement:
--   For a prime $q \nmid 104$, the unique integral extension of an endomorphism of the original rational Picard scheme preserves identity and composition. Define the integral scalar-nineteen endomorphism as the unique extension of the actual rational multiplication-by-nineteen morphism. The two integral norm maps have both composites equal to this extension:
--
--   $$\Pi\circ\overline\Pi=\overline\Pi\circ\Pi=[19]_{\mathrm{extension}}.$$
--
--   This constructor interface preserves the same local Picard model and both specific rational norm maps. Identifying the extension with multiplication by nineteen for the local relative group law is a subsequent obligation.
-- source:
--   MazurTheorem, Order13GoodPrimeIntegralNormComposition.lean, all eight original declarations and the original group provider, full source SHA-256 be8d656da031ebd7324adb2ed6f1fca69e32ebc8af7916705d0489fa5273eca4, Apache-2.0. Complete original types and nonproof values checked.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: uniqueness of Neron extension preserves identities and
composition for the SAME actual rational Picard endomorphisms.
Named downstream consumer: integral norm factorization and its good-prime
kernel fibres. The scalar nineteen here is defined as the unique integral
extension of the actual rational scalar map; its comparison with the
local relative group law is a separate downstream obligation.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNineteenNorm_schemePi_comp_schemePiConjugate
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNineteenNorm_schemePiConjugate_comp_schemePi
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

noncomputable section
namespace MazurTransfer.Order13GoodPrimeIntegralNormComposition
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalPicardModels Order13LocalIntegralCoefficientMaps
open Order13GoodPrimeLocalGenericPicardComparison
open Order13GoodPrimeIntegralNormExtensions
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
local instance integralNormCompositionOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) := actualGroup

theorem localGenericNorm_comp
    (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    localGenericNorm q hq (φ ≫ ψ) =
      schemeHomOverComp (localGenericNorm q hq φ) (localGenericNorm q hq ψ) := by
  apply Subtype.ext
  change (((actualLocalGenericOverIso q hq).inv ≫ (φ ≫ ψ) ≫
    (actualLocalGenericOverIso q hq).hom).left) =
    (((actualLocalGenericOverIso q hq).inv ≫ φ ≫
      (actualLocalGenericOverIso q hq).hom).left ≫
      ((actualLocalGenericOverIso q hq).inv ≫ ψ ≫
      (actualLocalGenericOverIso q hq).hom).left)
  rw [← Over.comp_left]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem localGenericNorm_id :
    localGenericNorm q hq (𝟙 (Over.mk actualPicard.toBase)) =
      schemeHomOverId (localGenericPicard q hq).toBase := by
  apply Subtype.ext
  change (((actualLocalGenericOverIso q hq).inv ≫ 𝟙 _ ≫
    (actualLocalGenericOverIso q hq).hom).left) = 𝟙 _
  simp only [Category.id_comp, Iso.inv_hom_id, Over.id_left]

theorem integralNorm_comp
    (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    integralNorm q hq (φ ≫ ψ) =
      schemeHomOverComp (integralNorm q hq φ) (integralNorm q hq ψ) := by
  symm
  apply integralNorm_unique
  rw [genericFibreRestrict_endComp, integralNorm_restrict, integralNorm_restrict,
    ← localGenericNorm_comp]

theorem integralNorm_id :
    integralNorm q hq (𝟙 (Over.mk actualPicard.toBase)) =
      schemeHomOverId (localPicard q hq).toBase := by
  symm
  apply integralNorm_unique
  rw [genericFibreRestrict_schemeHomOverId, localGenericNorm_id]
  rfl

def integralScalarNineteen :=
  integralNorm q hq ((𝟙 (Over.mk actualPicard.toBase)) ^ 19)

theorem integralPi_comp_integralPiConjugate :
    schemeHomOverComp (integralPi q hq) (integralPiConjugate q hq) =
      integralScalarNineteen q hq := by
  change schemeHomOverComp (integralNorm q hq schemePi)
    (integralNorm q hq schemePiConjugate) = _
  rw [← integralNorm_comp, schemePi_comp_schemePiConjugate]
  rfl

theorem integralPiConjugate_comp_integralPi :
    schemeHomOverComp (integralPiConjugate q hq) (integralPi q hq) =
      integralScalarNineteen q hq := by
  change schemeHomOverComp (integralNorm q hq schemePiConjugate)
    (integralNorm q hq schemePi) = _
  rw [← integralNorm_comp, schemePiConjugate_comp_schemePi]
  rfl

theorem integralNorms_commute :
    schemeHomOverComp (integralPi q hq) (integralPiConjugate q hq) =
      schemeHomOverComp (integralPiConjugate q hq) (integralPi q hq) :=
  (integralPi_comp_integralPiConjugate q hq).trans
    (integralPiConjugate_comp_integralPi q hq).symm

end MazurTransfer.Order13GoodPrimeIntegralNormComposition
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormComposition.integralNorm_comp
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormComposition.integralNorm_id
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormComposition.integralPi_comp_integralPiConjugate
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormComposition.integralPiConjugate_comp_integralPi
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormComposition.integralNorms_commute

#print axioms MazurTransfer.Order13GoodPrimeIntegralNormComposition.localGenericNorm_comp
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormComposition.localGenericNorm_id
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormComposition.integralScalarNineteen


