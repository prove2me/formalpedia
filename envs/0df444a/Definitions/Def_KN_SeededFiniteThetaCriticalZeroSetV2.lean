-- Prove2me | Definitions.Def_KN_SeededFiniteThetaCriticalZeroSetV2
-- name    : KN_SeededFiniteThetaCriticalZeroSetV2
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T11:18:01.583911+00:00
-- url     : https://prove2.me/theorems/d432baa2-36ea-40c6-bfca-27ed9193c4e6
-- title:
--   Critical-value zero sets for rebased finite theta data
-- statement:
--   Evaluation and seeded critical-value zero-set predicates for finite theta data, rebuilt over `KN_SeededThetaConstructionV3`.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Sections 4–5.

import Definitions.Def_KN_SeededThetaConstructionV3

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Evaluation of the finite theta element at the finite-order horizontal
character indexing the same finite quotient. -/
def SeededFiniteThetaDataV2.eval
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (Θ : SeededFiniteThetaDataV2 L)
    (χ : HorizontalCharacter p L.exponent) : ℂ_[p] :=
  (Θ.theta χ.support).coeff.sum fun g a =>
    (a : ℂ_[p]) * χ.toMonoidHom g

/-- The finite theta elements have the same character zeroes as the seeded
central critical values.  This is the zero-set consequence of the explicit
Birch--Stevens evaluation formula; it is recorded for the very same theta
elements that occur in the norm relations. -/
def SeededFiniteThetaDataV2.HasSeededCriticalZeroSet
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (Θ : SeededFiniteThetaDataV2 L) : Prop :=
  ∀ χ, Θ.eval χ ≠ 0 ↔
    let θ := primitiveProductV2 η (Θ.characters.realized χ)
    @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
      (k / 2 - 1) ≠ 0

end HorizontalPadicL


