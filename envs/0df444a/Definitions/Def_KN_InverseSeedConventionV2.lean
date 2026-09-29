-- Prove2me | Definitions.Def_KN_InverseSeedConventionV2
-- name    : KN_InverseSeedConventionV2
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T11:19:03.610236+00:00
-- url     : https://prove2.me/theorems/261544c7-9922-4933-851c-9814969f1f2e
-- title:
--   Inverse-seed horizontal construction over rebased data
-- statement:
--   The corrected inverse-seed convention, including orderly prime systems, faithful character realization, horizontal measures, finite theta data, normalized measures, and interpolation, rebuilt entirely over the rebased definition spine.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Sections 4–5.

import Definitions.Def_KN_SeededHorizontalPadicLFunctionV3B
import Definitions.Def_KN_SeededFiniteThetaCriticalZeroSetV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Corrected convention: MTT.criticalLValue eta is the inverse-character twist.
Orderliness therefore uses eta*a_l - eta^2 - epsilon, equivalently the usual
Euler expression for f tensor eta^{-1}. Interpolation still uses eta itself. -/
def IsOrderlyPrimeForSeededEigenformV3
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (p m : ℕ) [Fact p.Prime] (ιp : MTT.Qbar →+* ℂ_[p])
    (f : MTT.Eigenform N k ι) (η : DirichletCharacterWithLevel)
    (ℓ : ℕ) : Prop :=
  ℓ.Prime ∧ Nat.ModEq (p ^ m) ℓ 1 ∧
    Nat.Coprime ℓ (N * η.2.conductor) ∧
    ‖ιp (η.2 ℓ * f.coeff ℓ - (η.2 ℓ) ^ 2 - f.epsilon ℓ)‖ = 1

structure SeededHorizontalPrimeSystemV3
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
    IsOrderlyPrimeForSeededEigenformV3 p orderExponent ιp f η (primeAt n)
  naturalDensity : ℝ
  naturalDensity_pos : 0 < naturalDensity
  has_naturalDensity :
    HasPrimeNaturalDensity {ℓ : ℕ | ∃ n : ℕ, primeAt n = ℓ} naturalDensity

def SeededHorizontalPrimeSystemV3.exponent
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeSystemV3 p ιp f η B) (n : ℕ) : ℕ :=
  padicValNat p (L.primeAt n - 1)

structure SeededHorizontalPadicLFunctionV4
    {N k B : ℕ} {ι : MTT.Qbar →+* ℂ} (p : ℕ) [Fact p.Prime]
    (ιp : MTT.Qbar →+* ℂ_[p]) (f : MTT.Eigenform N k ι)
    (η : DirichletCharacterWithLevel) where
  primes : SeededHorizontalPrimeSystemV3 p ιp f η B
  coefficientRing : Subring ℂ_[p]
  coefficient_integral : ∀ x : coefficientRing, (x : ℂ_[p]) ∈ 𝓞_ℂ_[p]
  measure : HorizontalMeasure coefficientRing p primes.exponent


structure SeededHorizontalPrimeDataV3
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
    IsOrderlyPrimeForSeededEigenformV3 p orderExponent ιp f η (primeAt n)

def SeededHorizontalPrimeSystemV3.toConstructionData
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeSystemV3 p ιp f η B) :
    SeededHorizontalPrimeDataV3 p ιp f η B where
  orderExponent := L.orderExponent
  orderExponent_pos := L.orderExponent_pos
  primeAt := L.primeAt
  primeAt_prime := L.primeAt_prime
  primeAt_injective := L.primeAt_injective
  primeAt_avoids := L.primeAt_avoids
  primeAt_orderly := L.primeAt_orderly

def SeededHorizontalPrimeDataV3.exponent
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B) (n : ℕ) : ℕ :=
  padicValNat p (L.primeAt n - 1)


/-- The squarefree product of the selected auxiliary primes indexed by `A`. -/
def SeededHorizontalPrimeDataV3.supportModulus
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B) (A : Finset ℕ) : ℕ :=
  ∏ n ∈ A, L.primeAt n

theorem SeededHorizontalPrimeDataV3.supportModulus_pos
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B) (A : Finset ℕ) :
    0 < L.supportModulus A := by
  exact Finset.prod_pos fun n _ => (L.primeAt_prime n).pos

/-- The quotient maps chosen in equation (5.1) of Kriz--Nordentoft.

For every auxiliary prime `ℓₙ`, this records a surjection from
`(Z/ℓₙZ)ˣ` onto its maximal `p`-power cyclic quotient
`Z / p^(vₚ(ℓₙ-1)) Z`. -/
structure SeededHorizontalProjectionSystemV3
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B) where
  localProjection : ∀ n,
    (ZMod (L.primeAt n))ˣ →*
      Multiplicative (ZMod (p ^ L.exponent n))
  localProjection_surjective :
    ∀ n, Function.Surjective (localProjection n)

/-- The product of the chosen local quotient maps over a finite support.

The reduction from the product modulus to each prime modulus is canonical;
the noncanonical choices are precisely the maps stored in
`SeededHorizontalProjectionSystemV3.localProjection`. -/
def SeededHorizontalProjectionSystemV3.supportProjection
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalProjectionSystemV3 L) (A : Finset ℕ) :
    (ZMod (L.supportModulus A))ˣ →*
      HorizontalFiniteGroup p L.exponent A :=
  MonoidHom.pi fun i =>
    (R.localProjection i.1).comp
      (ZMod.unitsMap (Finset.dvd_prod_of_mem L.primeAt i.2))

/-- A faithful realization of horizontal characters as Dirichlet characters.

The character `atLevel χ` is allowed to be imprimitive at the full product
modulus.  The compatibility equation says that, after applying the fixed
embedding into `ℂ_[p]`, it is exactly the pullback of the horizontal character
along the product of the quotient maps from equation (5.1). -/
structure SeededHorizontalCharacterRealizationV3
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B) where
  projections : SeededHorizontalProjectionSystemV3 L
  atLevel : ∀ χ : HorizontalCharacter p L.exponent,
    DirichletCharacter MTT.Qbar (L.supportModulus χ.support)
  atLevel_compatibility :
    ∀ (χ : HorizontalCharacter p L.exponent)
      (u : (ZMod (L.supportModulus χ.support))ˣ),
      ιp (atLevel χ (u : ZMod (L.supportModulus χ.support))) =
        χ.toMonoidHom (projections.supportProjection χ.support u)

/-- The primitive character underlying the faithful full-level realization. -/
noncomputable def SeededHorizontalCharacterRealizationV3.realized
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (χ : HorizontalCharacter p L.exponent) :
    DirichletCharacterWithLevel := by
  let ψ := R.atLevel χ
  letI : NeZero (L.supportModulus χ.support) :=
    ⟨Nat.ne_of_gt (L.supportModulus_pos χ.support)⟩
  exact ⟨⟨ψ.conductor, Nat.pos_of_ne_zero ψ.conductor_ne_zero⟩,
    ψ.primitiveCharacter⟩

theorem SeededHorizontalCharacterRealizationV3.realized_primitive
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (χ : HorizontalCharacter p L.exponent) :
    (R.realized χ).2.IsPrimitive := by
  letI : NeZero (L.supportModulus χ.support) :=
    ⟨Nat.ne_of_gt (L.supportModulus_pos χ.support)⟩
  unfold realized
  dsimp only
  exact DirichletCharacter.primitiveCharacter_isPrimitive _

theorem SeededHorizontalCharacterRealizationV3.realized_conductor_dvd
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (χ : HorizontalCharacter p L.exponent) :
    (R.realized χ).2.conductor ∣ L.supportModulus χ.support := by
  letI : NeZero (L.supportModulus χ.support) :=
    ⟨Nat.ne_of_gt (L.supportModulus_pos χ.support)⟩
  calc
    (R.realized χ).2.conductor ∣ (R.realized χ).1.1 :=
      DirichletCharacter.conductor_dvd_level _
    _ = (R.atLevel χ).conductor := by rfl
    _ ∣ L.supportModulus χ.support :=
      DirichletCharacter.conductor_dvd_level _

/-- The properties needed later for interpolation and counting.  Unlike the
old structure, these are conclusions to be proved from the pullback equation,
not unconstrained fields in the realization data. -/
def SeededHorizontalCharacterRealizationV3.HasExpectedProperties
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L) : Prop :=
  (∀ χ, orderOf (R.realized χ).2 = orderOf χ.toMonoidHom) ∧
  R.realized (trivialHorizontalCharacterV2 p L.exponent) =
    trivialCharacterWithLevelV2 ∧
  ∀ ψ : DirichletCharacterWithLevel,
    ψ.2.IsPrimitive →
    (∃ a : ℕ, orderOf ψ.2 = p ^ a) →
    (∃ A : Finset ℕ, ψ.2.conductor ∣ L.supportModulus A) →
    ∃ χ : HorizontalCharacter p L.exponent, R.realized χ = ψ


/-- The faithful interpolation contract for a seeded horizontal `p`-adic
L-function.  The Dirichlet characters are obtained from the actual quotient
maps used to push forward the theta elements. -/
def SeededHorizontalPadicLFunctionV4.InterpolatesSeededCriticalValuesV4
    {N k B p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (ν : SeededHorizontalPadicLFunctionV4 (B := B) p ιp f η) : Prop :=
  ∃ R : SeededHorizontalCharacterRealizationV3 ν.primes.toConstructionData,
    R.HasExpectedProperties ∧
    ∀ χ, ν.measure.eval χ ≠ 0 ↔
      let θ := primitiveProductV2 η (R.realized χ)
      @MTT.criticalLValue ι f.form
        θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2 (k / 2 - 1) ≠ 0

/-- The one-sign seeded construction needed for Corollary 5.17.  The prime
`p` is required to be odd, so every horizontal character of `p`-power order
is even and the appropriately signed theta measure interpolates every character in the
horizontal family. -/
def HasSeededHorizontalPadicLConstructionV4
    {N k : ℕ} (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) : Prop :=
  ∀ (η : DirichletCharacterWithLevel)
    (_hηprim : η.2.IsPrimitive)
    (_hηeven : η.2 (-1) = 1)
    (p m B : ℕ) [Fact p.Prime]
    (_hpodd : p ≠ 2)
    (_hm : 0 < m) (_hB : 0 < B)
    (_hηorder : 2 ≤ orderOf η.2)
    (_horderCoprime : Nat.Coprime (orderOf η.2) p)
    (_hηcoprime : Nat.Coprime (N * p) η.2.conductor)
    (_hseedNonzero :
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0),
    ∃ (ιp : MTT.Qbar →+* ℂ_[p])
      (ν : SeededHorizontalPadicLFunctionV4 (B := B) p ιp f η),
      ν.primes.orderExponent = m ∧
      ν.InterpolatesSeededCriticalValuesV4 ∧
      ν.measure.eval (trivialHorizontalCharacterV2 p ν.primes.exponent) ≠ 0


/-- Finite-level theta data using the faithful horizontal-character
realization. -/
structure SeededFiniteThetaDataV3
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B) where
  coefficientRing : Subring ℂ_[p]
  coefficientRing_eq : coefficientRing = (𝓞_ℂ_[p]).toSubring
  coefficient_integral : ∀ x : coefficientRing, (x : ℂ_[p]) ∈ 𝓞_ℂ_[p]
  characters : SeededHorizontalCharacterRealizationV3 L
  theta : ∀ A : Finset ℕ, HorizontalGroupAlgebra coefficientRing p L.exponent A
  eulerFactor : ∀ (A : Finset ℕ) (n : ℕ),
    HorizontalGroupAlgebra coefficientRing p L.exponent A
  eulerFactor_augmentation_norm : ∀ (A : Finset ℕ) (n : ℕ),
    ‖((horizontalAugmentation (eulerFactor A n) : coefficientRing) : ℂ_[p])‖ =
      ‖ιp (η.2 (L.primeAt n) * f.coeff (L.primeAt n) -
        (η.2 (L.primeAt n)) ^ 2 - f.epsilon (L.primeAt n))‖

def SeededFiniteThetaDataV3.SatisfiesNormRelations
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) : Prop :=
  ∀ (A : Finset ℕ) (n : ℕ) (hn : n ∉ A),
    horizontalGroupAlgebraProjection Θ.coefficientRing (Finset.subset_insert n A)
      (Θ.theta (insert n A)) = Θ.eulerFactor A n * Θ.theta A

def SeededFiniteThetaDataV3.HasUnitEulerFactors
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) : Prop :=
  ∀ (A : Finset ℕ) (n : ℕ), IsUnit (Θ.eulerFactor A n)

/-- The compatible normalized theta measure, retaining the faithful quotient
maps and character realization used in its construction. -/
structure SeededNormalizedThetaMeasureV3
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B) where
  coefficientRing : Subring ℂ_[p]
  coefficientRing_eq : coefficientRing = (𝓞_ℂ_[p]).toSubring
  coefficient_integral : ∀ x : coefficientRing, (x : ℂ_[p]) ∈ 𝓞_ℂ_[p]
  characters : SeededHorizontalCharacterRealizationV3 L
  measure : HorizontalMeasure coefficientRing p L.exponent

def SeededNormalizedThetaMeasureV3.InterpolatesSeededCriticalValues
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (μ : SeededNormalizedThetaMeasureV3 L) : Prop :=
  ∀ χ, μ.measure.eval χ ≠ 0 ↔
    let θ := primitiveProductV2 η (μ.characters.realized χ)
    @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
      (k / 2 - 1) ≠ 0


/-- Evaluation of the finite theta element at the finite-order horizontal
character indexing the same finite quotient. -/
def SeededFiniteThetaDataV3.eval
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L)
    (χ : HorizontalCharacter p L.exponent) : ℂ_[p] :=
  (Θ.theta χ.support).coeff.sum fun g a =>
    (a : ℂ_[p]) * χ.toMonoidHom g

/-- The finite theta elements have the same character zeroes as the seeded
central critical values.  This is the zero-set consequence of the explicit
Birch--Stevens evaluation formula; it is recorded for the very same theta
elements that occur in the norm relations. -/
def SeededFiniteThetaDataV3.HasSeededCriticalZeroSet
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) : Prop :=
  ∀ χ, Θ.eval χ ≠ 0 ↔
    let θ := primitiveProductV2 η (Θ.characters.realized χ)
    @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
      (k / 2 - 1) ≠ 0


end HorizontalPadicL


