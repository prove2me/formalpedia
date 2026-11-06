-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
-- name    : QEC_Coding_BalancedProduct_TannerExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:03:45.481926+00:00
-- url     : https://prove2.me/theorems/48798035-9c7d-4d1d-9a3a-0fd74f8b9932
-- title:
--   Tanner Expansion
-- statement:
--   Definitions and structural lemmas for Tanner Expansion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/TannerExpansion.lean

import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
namespace QEC.Coding
end QEC.Coding
namespace LinearMap
open QEC.Coding
universe u v w
def SmallSetExpanding
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (f : Word F ι →ₗ[F] Word F κ)
    (radius expansionNumerator expansionDenominator : Nat) : Prop :=
  0 < expansionDenominator ∧
    ∀ x : Word F ι,
      HammingWeight x ≤ radius →
      expansionNumerator * HammingWeight x ≤
        expansionDenominator * HammingWeight (f x)
def SmallSetExpandingAtRelativeRadius
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (f : Word F ι →ₗ[F] Word F κ)
    (radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat) : Prop :=
  0 < radiusDenominator ∧ 0 < expansionDenominator ∧
    ∀ x : Word F ι,
      radiusDenominator * HammingWeight x ≤
          radiusNumerator * Fintype.card ι →
      expansionNumerator * HammingWeight x ≤
        expansionDenominator * HammingWeight (f x)
end LinearMap


