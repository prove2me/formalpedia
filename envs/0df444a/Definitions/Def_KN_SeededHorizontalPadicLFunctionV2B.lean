-- Prove2me | Definitions.Def_KN_SeededHorizontalPadicLFunctionV2B
-- name    : KN_SeededHorizontalPadicLFunctionV2B
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T11:06:29.149479+00:00
-- url     : https://prove2.me/theorems/6bacf7e7-62af-4849-a228-729e56eb7ced
-- title:
--   Rebased seeded horizontal p-adic L-function data
-- statement:
--   Foundational data for the seeded horizontal p-adic L-function construction, rebased on `KN_HorizontalPadicLAux`. It defines primitive products of Dirichlet characters, trivial horizontal characters, orderly seeded primes, positive-density seeded prime systems, and the associated horizontal measure. The superseded V2 interpolation predicate and construction-existence predicate are intentionally omitted.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Sections 4–5.

import Definitions.Def_KN_HorizontalPadicLAux

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

noncomputable def primitiveProductV2
    (χ ψ : DirichletCharacterWithLevel) : DirichletCharacterWithLevel := by
  letI : NeZero χ.1.1 := ⟨Nat.ne_of_gt χ.1.2⟩
  letI : NeZero ψ.1.1 := ⟨Nat.ne_of_gt ψ.1.2⟩
  letI : NeZero (Nat.lcm χ.1.1 ψ.1.1) :=
    ⟨Nat.lcm_ne_zero (Nat.ne_of_gt χ.1.2) (Nat.ne_of_gt ψ.1.2)⟩
  let φ := χ.2.mul ψ.2
  have hφ : φ.conductor ≠ 0 := φ.conductor_ne_zero
  exact ⟨⟨φ.conductor, Nat.pos_of_ne_zero hφ⟩, φ.primitiveCharacter⟩

def trivialCharacterWithLevelV2 : DirichletCharacterWithLevel :=
  ⟨⟨1, Nat.zero_lt_one⟩, 1⟩

def trivialHorizontalCharacterV2 (p : ℕ) [Fact p.Prime] (m : ℕ → ℕ) :
    HorizontalCharacter p m where
  support := ∅
  toMonoidHom := 1

def IsOrderlyPrimeForSeededEigenformV2
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (p m : ℕ) [Fact p.Prime] (ιp : MTT.Qbar →+* ℂ_[p])
    (f : MTT.Eigenform N k ι) (η : DirichletCharacterWithLevel)
    (ℓ : ℕ) : Prop :=
  ℓ.Prime ∧ Nat.ModEq (p ^ m) ℓ 1 ∧
    Nat.Coprime ℓ (N * η.2.conductor) ∧
    ‖ιp (η.2 ℓ * f.coeff ℓ - 1 - (η.2 ℓ) ^ 2 * f.epsilon ℓ)‖ = 1

structure SeededHorizontalPrimeSystemV2
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (p : ℕ) [Fact p.Prime] (ιp : MTT.Qbar →+* ℂ_[p])
    (f : MTT.Eigenform N k ι) (η : DirichletCharacterWithLevel) (B : ℕ) where
  orderExponent : ℕ
  orderExponent_pos : 0 < orderExponent
  primeAt : ℕ → ℕ
  primeAt_prime : ∀ n, (primeAt n).Prime
  primeAt_injective : Function.Injective primeAt
  primeAt_avoids : ∀ n, Nat.Coprime (primeAt n) B
  primeAt_orderly : ∀ n,
    IsOrderlyPrimeForSeededEigenformV2 p orderExponent ιp f η (primeAt n)
  naturalDensity : ℝ
  naturalDensity_pos : 0 < naturalDensity
  has_naturalDensity :
    HasPrimeNaturalDensity {ℓ : ℕ | ∃ n : ℕ, primeAt n = ℓ} naturalDensity

def SeededHorizontalPrimeSystemV2.exponent
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeSystemV2 p ιp f η B) (n : ℕ) : ℕ :=
  padicValNat p (L.primeAt n - 1)

structure SeededHorizontalPadicLFunctionV2
    {N k B : ℕ} {ι : MTT.Qbar →+* ℂ} (p : ℕ) [Fact p.Prime]
    (ιp : MTT.Qbar →+* ℂ_[p]) (f : MTT.Eigenform N k ι)
    (η : DirichletCharacterWithLevel) where
  primes : SeededHorizontalPrimeSystemV2 p ιp f η B
  coefficientRing : Subring ℂ_[p]
  coefficient_integral : ∀ x : coefficientRing, (x : ℂ_[p]) ∈ 𝓞_ℂ_[p]
  measure : HorizontalMeasure coefficientRing p primes.exponent

end HorizontalPadicL


