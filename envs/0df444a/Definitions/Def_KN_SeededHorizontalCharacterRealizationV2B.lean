-- Prove2me | Definitions.Def_KN_SeededHorizontalCharacterRealizationV2B
-- name    : KN_SeededHorizontalCharacterRealizationV2B
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T11:13:42.94365+00:00
-- url     : https://prove2.me/theorems/08cec8ec-0573-4403-9623-01c8189c548b
-- title:
--   Horizontal character realization over rebased theta data
-- statement:
--   Projection systems and faithful realization of finite horizontal characters as primitive Dirichlet characters, rebased on `KN_SeededThetaConstructionV2B`.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Sections 4–5.

import Definitions.Def_KN_SeededThetaConstructionV2B
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Units.Hom

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- The squarefree product of the selected auxiliary primes indexed by `A`. -/
def SeededHorizontalPrimeDataV2.supportModulus
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV2 p ιp f η B) (A : Finset ℕ) : ℕ :=
  ∏ n ∈ A, L.primeAt n

theorem SeededHorizontalPrimeDataV2.supportModulus_pos
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV2 p ιp f η B) (A : Finset ℕ) :
    0 < L.supportModulus A := by
  exact Finset.prod_pos fun n _ => (L.primeAt_prime n).pos

/-- The quotient maps chosen in equation (5.1) of Kriz--Nordentoft.

For every auxiliary prime `ℓₙ`, this records a surjection from
`(Z/ℓₙZ)ˣ` onto its maximal `p`-power cyclic quotient
`Z / p^(vₚ(ℓₙ-1)) Z`. -/
structure SeededHorizontalProjectionSystem
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV2 p ιp f η B) where
  localProjection : ∀ n,
    (ZMod (L.primeAt n))ˣ →*
      Multiplicative (ZMod (p ^ L.exponent n))
  localProjection_surjective :
    ∀ n, Function.Surjective (localProjection n)

/-- The product of the chosen local quotient maps over a finite support.

The reduction from the product modulus to each prime modulus is canonical;
the noncanonical choices are precisely the maps stored in
`SeededHorizontalProjectionSystem.localProjection`. -/
def SeededHorizontalProjectionSystem.supportProjection
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (R : SeededHorizontalProjectionSystem L) (A : Finset ℕ) :
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
structure SeededHorizontalCharacterRealizationV2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV2 p ιp f η B) where
  projections : SeededHorizontalProjectionSystem L
  atLevel : ∀ χ : HorizontalCharacter p L.exponent,
    DirichletCharacter MTT.Qbar (L.supportModulus χ.support)
  atLevel_compatibility :
    ∀ (χ : HorizontalCharacter p L.exponent)
      (u : (ZMod (L.supportModulus χ.support))ˣ),
      ιp (atLevel χ (u : ZMod (L.supportModulus χ.support))) =
        χ.toMonoidHom (projections.supportProjection χ.support u)

/-- The primitive character underlying the faithful full-level realization. -/
noncomputable def SeededHorizontalCharacterRealizationV2.realized
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV2 L)
    (χ : HorizontalCharacter p L.exponent) :
    DirichletCharacterWithLevel := by
  let ψ := R.atLevel χ
  letI : NeZero (L.supportModulus χ.support) :=
    ⟨Nat.ne_of_gt (L.supportModulus_pos χ.support)⟩
  exact ⟨⟨ψ.conductor, Nat.pos_of_ne_zero ψ.conductor_ne_zero⟩,
    ψ.primitiveCharacter⟩

theorem SeededHorizontalCharacterRealizationV2.realized_primitive
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV2 L)
    (χ : HorizontalCharacter p L.exponent) :
    (R.realized χ).2.IsPrimitive := by
  letI : NeZero (L.supportModulus χ.support) :=
    ⟨Nat.ne_of_gt (L.supportModulus_pos χ.support)⟩
  unfold realized
  dsimp only
  exact DirichletCharacter.primitiveCharacter_isPrimitive _

theorem SeededHorizontalCharacterRealizationV2.realized_conductor_dvd
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV2 L)
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
def SeededHorizontalCharacterRealizationV2.HasExpectedProperties
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV2 L) : Prop :=
  (∀ χ, orderOf (R.realized χ).2 = orderOf χ.toMonoidHom) ∧
  R.realized (trivialHorizontalCharacterV2 p L.exponent) =
    trivialCharacterWithLevelV2 ∧
  ∀ ψ : DirichletCharacterWithLevel,
    ψ.2.IsPrimitive →
    (∃ a : ℕ, orderOf ψ.2 = p ^ a) →
    (∃ A : Finset ℕ, ψ.2.conductor ∣ L.supportModulus A) →
    ∃ χ : HorizontalCharacter p L.exponent, R.realized χ = ψ

end HorizontalPadicL


