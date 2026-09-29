-- Prove2me | Definitions.Def_KN_SeededThetaConstructionV2B
-- name    : KN_SeededThetaConstructionV2B
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T11:09:24.150441+00:00
-- url     : https://prove2.me/theorems/6a453bf9-14a5-4d99-8e93-ae731af96db8
-- title:
--   Seeded theta construction over the rebased V2 data
-- statement:
--   Finite-level seeded theta data, character realization, normalized measures, and their interpolation interfaces, formulated over the rebased `KN_SeededHorizontalPadicLFunctionV2B` definitions.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Sections 4–5.

import Definitions.Def_KN_SeededHorizontalPadicLFunctionV2B
import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- The part of a seeded horizontal prime system used to construct theta elements.
It deliberately omits the positive-density data, which is used only in the later
counting argument. -/
structure SeededHorizontalPrimeDataV2
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

def SeededHorizontalPrimeSystemV2.toConstructionData
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeSystemV2 p ιp f η B) :
    SeededHorizontalPrimeDataV2 p ιp f η B where
  orderExponent := L.orderExponent
  orderExponent_pos := L.orderExponent_pos
  primeAt := L.primeAt
  primeAt_prime := L.primeAt_prime
  primeAt_injective := L.primeAt_injective
  primeAt_avoids := L.primeAt_avoids
  primeAt_orderly := L.primeAt_orderly

def SeededHorizontalPrimeDataV2.exponent
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV2 p ιp f η B) (n : ℕ) : ℕ :=
  padicValNat p (L.primeAt n - 1)

/-- A simultaneous realization of characters of the horizontal finite quotients
as primitive Dirichlet characters supported on the chosen auxiliary primes. -/
structure SeededHorizontalCharacterRealization
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV2 p ιp f η B) where
  realized : HorizontalCharacter p L.exponent → DirichletCharacterWithLevel
  primitive : ∀ χ, (realized χ).2.IsPrimitive
  order_dvd : ∀ χ, ∃ a ≤ L.orderExponent,
    orderOf (realized χ).2 = p ^ a
  trivial : realized (trivialHorizontalCharacterV2 p L.exponent) =
    trivialCharacterWithLevelV2
  conductor_dvd : ∀ χ, (realized χ).2.conductor ∣
    ∏ n ∈ χ.support, L.primeAt n
  surjective_on_exact_order : ∀ χ : DirichletCharacterWithLevel,
    χ.2.IsPrimitive → orderOf χ.2 = p ^ L.orderExponent →
    (∃ A : Finset ℕ, χ.2.conductor ∣ ∏ n ∈ A, L.primeAt n) →
    ∃ ψ : HorizontalCharacter p L.exponent, realized ψ = χ

/-- The signed modular symbol whose algebraic normalization is supplied by a
period system. -/
def signedModularSymbol (f : UpperHalfPlane → ℂ) (s : Bool)
    (j : ℕ) (a m : ℚ) : ℂ :=
  (MTT.modularSymbol f j a m +
    (MTT.sign s : ℂ) * (-1 : ℂ) ^ j * MTT.modularSymbol f j (-a) m) / 2

/-- The common denominator-clearing datum obtained from the finitely generated
period lattice. -/
structure IntegralPeriodScale {N k p : ℕ} {ι : MTT.Qbar →+* ℂ}
    [Fact p.Prime] (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p])
    (P : MTT.Periods k ι f.form) where
  scale : MTT.Qbar
  scale_ne_zero : scale ≠ 0
  integral_value : ∀ s j r, j ≤ k - 2 →
    ιp (scale * P.value s j r) ∈ 𝓞_ℂ_[p]

abbrev HorizontalGroupAlgebra (R : Type*) [CommRing R]
    (p : ℕ) (m : ℕ → ℕ) (A : Finset ℕ) :=
  MonoidAlgebra R (HorizontalFiniteGroup p m A)

def horizontalRestrictionHom {p : ℕ} {m : ℕ → ℕ} {A B : Finset ℕ}
    (hAB : A ⊆ B) :
    HorizontalFiniteGroup p m B →* HorizontalFiniteGroup p m A where
  toFun := restrictHorizontalCoordinates hAB
  map_one' := rfl
  map_mul' _ _ := rfl

def horizontalGroupAlgebraProjection (R : Type*) [CommRing R]
    {p : ℕ} {m : ℕ → ℕ} {A B : Finset ℕ} (hAB : A ⊆ B) :
    HorizontalGroupAlgebra R p m B →+* HorizontalGroupAlgebra R p m A :=
  MonoidAlgebra.mapDomainRingHom R (horizontalRestrictionHom hAB)

def horizontalAugmentation {R : Type*} [CommRing R] {p : ℕ}
    {m : ℕ → ℕ} {A : Finset ℕ} (θ : HorizontalGroupAlgebra R p m A) : R :=
  MonoidAlgebra.lift R R (HorizontalFiniteGroup p m A) 1 θ

/-- Unnormalised finite-level theta elements and their Euler transition factors.
The actual norm relation and invertibility of the factors are separate properties. -/
structure SeededFiniteThetaData
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV2 p ιp f η B) where
  coefficientRing : Subring ℂ_[p]
  coefficientRing_eq : coefficientRing = (𝓞_ℂ_[p]).toSubring
  coefficient_integral : ∀ x : coefficientRing, (x : ℂ_[p]) ∈ 𝓞_ℂ_[p]
  characters : SeededHorizontalCharacterRealization L
  theta : ∀ A : Finset ℕ, HorizontalGroupAlgebra coefficientRing p L.exponent A
  eulerFactor : ∀ (A : Finset ℕ) (n : ℕ),
    HorizontalGroupAlgebra coefficientRing p L.exponent A
  eulerFactor_augmentation_norm : ∀ (A : Finset ℕ) (n : ℕ),
    ‖((horizontalAugmentation (eulerFactor A n) : coefficientRing) : ℂ_[p])‖ =
      ‖ιp (η.2 (L.primeAt n) * f.coeff (L.primeAt n) - 1 -
        (η.2 (L.primeAt n)) ^ 2 * f.epsilon (L.primeAt n))‖

def SeededFiniteThetaData.SatisfiesNormRelations
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (Θ : SeededFiniteThetaData L) : Prop :=
  ∀ (A : Finset ℕ) (n : ℕ) (hn : n ∉ A),
    horizontalGroupAlgebraProjection Θ.coefficientRing (Finset.subset_insert n A)
      (Θ.theta (insert n A)) = Θ.eulerFactor A n * Θ.theta A

def SeededFiniteThetaData.HasUnitEulerFactors
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (Θ : SeededFiniteThetaData L) : Prop :=
  ∀ (A : Finset ℕ) (n : ℕ), IsUnit (Θ.eulerFactor A n)

/-- The normalized compatible theta elements, before their interpolation theorem
is imposed. -/
structure SeededNormalizedThetaMeasure
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV2 p ιp f η B) where
  coefficientRing : Subring ℂ_[p]
  coefficientRing_eq : coefficientRing = (𝓞_ℂ_[p]).toSubring
  coefficient_integral : ∀ x : coefficientRing, (x : ℂ_[p]) ∈ 𝓞_ℂ_[p]
  characters : SeededHorizontalCharacterRealization L
  measure : HorizontalMeasure coefficientRing p L.exponent

def SeededNormalizedThetaMeasure.InterpolatesSeededCriticalValues
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (μ : SeededNormalizedThetaMeasure L) : Prop :=
  ∀ χ, μ.measure.eval χ ≠ 0 ↔
    let θ := primitiveProductV2 η (μ.characters.realized χ)
    @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
      (k / 2 - 1) ≠ 0

end HorizontalPadicL


