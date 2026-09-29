-- Prove2me | Definitions.Def_KN_SeedCyclotomicGaloisCharactersV3B
-- name    : KN_SeedCyclotomicGaloisCharactersV3B
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T11:17:29.493475+00:00
-- url     : https://prove2.me/theorems/99c96b11-b80e-46cf-ab4b-a2e95c1d2a2f
-- title:
--   Cyclotomic and seed Galois characters over rebased data
-- statement:
--   A finite Galois realization of the cyclotomic character and seed Dirichlet character, including compatibility with the Galois action on roots of unity, rebuilt over `KN_SeededPrimeGaloisDataV2`.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Section 4.3.

import Definitions.Def_KN_SeededPrimeGaloisDataV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- A common finite Galois realization of the cyclotomic character modulo
`p ^ m * N` and the finite character cut out by a Dirichlet seed.

The primitive root and `cyclotomicCharacter_spec` ensure that the first
character is the actual character describing the Galois action on roots of
unity, rather than an arbitrary homomorphism to the same unit group. -/
structure SeedCyclotomicGaloisCharacterDataV2
    (N p m : ℕ) (η : DirichletCharacterWithLevel) : Type 2 where
  L : Type
  [field_L : Field L]
  [numberField_L : NumberField L]
  [isGalois_L : IsGalois ℚ L]
  cyclotomicRoot : L
  cyclotomicRoot_primitive : IsPrimitiveRoot cyclotomicRoot (p ^ m * N)
  cyclotomicCharacter : (L ≃ₐ[ℚ] L) →* (ZMod (p ^ m * N))ˣ
  cyclotomicCharacter_spec : ∀ σ : L ≃ₐ[ℚ] L,
    σ cyclotomicRoot =
      cyclotomicRoot ^ ((cyclotomicCharacter σ : ZMod (p ^ m * N)).val)
  seedCharacter : (L ≃ₐ[ℚ] L) →* MTT.Qbarˣ
  seed_values_realized : ∀ a : (ZMod η.1.1)ˣ,
    ∃ σ : L ≃ₐ[ℚ] L,
      (seedCharacter σ : MTT.Qbar) = η.2 (a : ZMod η.1.1)
  only_seed_values : ∀ σ : L ≃ₐ[ℚ] L,
    ∃ a : (ZMod η.1.1)ˣ,
      (seedCharacter σ : MTT.Qbar) = η.2 (a : ZMod η.1.1)
  seedGenerator : L ≃ₐ[ℚ] L
  seedGenerator_order :
    orderOf (seedCharacter seedGenerator) = orderOf η.2

end HorizontalPadicL


