-- Prove2me | Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
-- name    : MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T04:25:24.952989+00:00
-- url     : https://prove2.me/theorems/7ddb7130-0238-4de8-99c5-0e2825633eb6
-- title:
--   Unique local integral extensions of the actual norm maps
-- statement:
--   Let $q$ be a prime not dividing $104$ and let $\mathcal J_q$ be the selected local Picard abelian scheme over $\mathbb Z_{(q)}$. Its Néron mapping property gives a unique integral extension of every endomorphism of the original rational Picard scheme, transported to the generic fibre by the canonical comparison. The constructors retain that extension, its exact generic-fibre restriction and its uniqueness.
--
--   Applying this construction to the two actual nineteen-norm maps defines their integral versions on $\mathcal J_q$. These maps are the input to the later finite étale and unramified Kummer arguments.
-- source:
--   MazurTheorem, Order13GoodPrimeIntegralNormExtensions.lean, complete original declarations (source SHA-256 dff035b4801e67c1abd608d991b3808b46949dd835fa09706d2f280a166e0ac2), Apache-2.0. Original declaration types and nonproof values checked in full. Official Anthropic FLT interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: extend the SAME actual rational norm endomorphisms
uniquely to the selected integral Picard family's local Z_(q) model,
using its proved abelian scheme and the complete FLT Neron mapping proof.
Named downstream consumer: good-prime finite etale norm fibres and
unramified local Kummer conditions.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericPicardComparisonDataNativeABIV3
import Theorems.Thm_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle

noncomputable section
namespace MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalPicardModels Order13LocalIntegralCoefficientMaps
open Order13GoodPrimeLocalGenericPicardComparison
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)

theorem localPicard_neron :
    NeronModelPropertyBundle (LocalRing q) ℚ (localPicard q hq).toBase :=
  NeronModelPropertyBundle.of_abelianSchemePropertyBundle (LocalRing q) ℚ
    (localPicard_abelian q hq)

theorem localNorm_unique_extension
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    ∃! ψ : SchemeHomOver (localPicard q hq).toBase (localPicard q hq).toBase,
      genericFibreRestrict (LocalRing q) ℚ (localPicard q hq).toBase
        (localPicard q hq).toBase ψ = localGenericNorm q hq φ :=
  (localPicard_neron q hq).existsUnique_extension
    (localPicard_geometry q hq).1 (localGenericNorm q hq φ)

def integralNorm
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    SchemeHomOver (localPicard q hq).toBase (localPicard q hq).toBase :=
  (localNorm_unique_extension q hq φ).choose

theorem integralNorm_restrict
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) :
    genericFibreRestrict (LocalRing q) ℚ (localPicard q hq).toBase
      (localPicard q hq).toBase (integralNorm q hq φ) = localGenericNorm q hq φ :=
  (localNorm_unique_extension q hq φ).choose_spec.1

theorem integralNorm_unique
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (ψ : SchemeHomOver (localPicard q hq).toBase (localPicard q hq).toBase)
    (hψ : genericFibreRestrict (LocalRing q) ℚ (localPicard q hq).toBase
      (localPicard q hq).toBase ψ = localGenericNorm q hq φ) :
    ψ = integralNorm q hq φ :=
  (localNorm_unique_extension q hq φ).choose_spec.2 ψ hψ

def integralPi := integralNorm q hq schemePi
def integralPiConjugate := integralNorm q hq schemePiConjugate

theorem actual_norms_have_unique_local_integral_extensions :
    (∃! ψ : SchemeHomOver (localPicard q hq).toBase (localPicard q hq).toBase,
      genericFibreRestrict (LocalRing q) ℚ (localPicard q hq).toBase
        (localPicard q hq).toBase ψ = localGenericPi q hq) ∧
    (∃! ψ : SchemeHomOver (localPicard q hq).toBase (localPicard q hq).toBase,
      genericFibreRestrict (LocalRing q) ℚ (localPicard q hq).toBase
        (localPicard q hq).toBase ψ = localGenericPiConjugate q hq) :=
  ⟨localNorm_unique_extension q hq schemePi,
    localNorm_unique_extension q hq schemePiConjugate⟩

end MazurTransfer.Order13GoodPrimeIntegralNormExtensions
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormExtensions.localPicard_neron
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormExtensions.integralNorm_restrict
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormExtensions.integralNorm_unique
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormExtensions.actual_norms_have_unique_local_integral_extensions

#print axioms MazurTransfer.Order13GoodPrimeIntegralNormExtensions.localNorm_unique_extension
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormExtensions.integralNorm
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormExtensions.integralPi
#print axioms MazurTransfer.Order13GoodPrimeIntegralNormExtensions.integralPiConjugate


