-- Prove2me | Definitions.Def_KN_PrimePowerPropagationV2
-- name    : KN_PrimePowerPropagationV2
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T11:18:04.327739+00:00
-- url     : https://prove2.me/theorems/ae9f89a7-fae8-41f2-86c8-269256c032f2
-- title:
--   Prime-power propagation over the rebased horizontal construction
-- statement:
--   Counting functions, character operations, finite-correction data, and prime-power propagation predicates, rebuilt over `KN_SeededHorizontalPadicLFunctionV3B`.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Sections 4–5.

import Definitions.Def_KN_SeededHorizontalPadicLFunctionV3B

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Count primitive characters in a specified set by their conductor. -/
def characterConductorCount (S : Set DirichletCharacterWithLevel) (X : ℝ) : ℕ :=
  Set.ncard {χ | χ ∈ S ∧ (χ.2.conductor : ℝ) ≤ X}

/-- New exact-order twists; nonvanishing concerns their primitive product with
the seed. The avoidance integer B can include future prime-power factors. -/
def seededPrimePowerTwists {N k : ℕ} (ι : MTT.Qbar →+* ℂ)
    (f : MTT.Eigenform N k ι) (η : DirichletCharacterWithLevel)
    (p m B : ℕ) : Set DirichletCharacterWithLevel :=
  {ψ | ψ.2.IsPrimitive ∧ orderOf ψ.2 = p ^ m ∧ ψ.2 (-1) = 1 ∧
    Nat.Coprime B ψ.2.conductor ∧
    let θ := primitiveProductV2 η ψ
    @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
      (k / 2 - 1) ≠ 0}

def seededPrimePowerNonvanishingCount {N k : ℕ} (ι : MTT.Qbar →+* ℂ)
    (f : MTT.Eigenform N k ι) (η : DirichletCharacterWithLevel)
    (p m B : ℕ) : ℝ → ℕ :=
  characterConductorCount (seededPrimePowerTwists ι f η p m B)

/-- Characters whose conductor is a squarefree product of selected primes,
excluding a finite set of indices reserved for Fourier corrections. -/
def supportedPrimePowerCharacters (ℓ : ℕ → ℕ) (A : Finset ℕ)
    (p m : ℕ) : Set DirichletCharacterWithLevel :=
  {ψ | ψ.2.IsPrimitive ∧ orderOf ψ.2 = p ^ m ∧
    ∃ S : Finset ℕ, Disjoint S A ∧ ψ.2.conductor ∣ ∏ n ∈ S, ℓ n}

/-- A conductor-controlled map with a uniform finite bound on every fibre.
It is defined on primitive Dirichlet characters, not on redundant presentations
of horizontal characters with arbitrarily enlarged supports. -/
structure CharacterCountingTransfer
    (S T : Set DirichletCharacterWithLevel) where
  map : S → T
  scale : ℝ
  scale_ge_one : 1 ≤ scale
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  conductor_bound : ∀ ψ,
    ((map ψ).val.2.conductor : ℝ) ≤ scale * (ψ.val.2.conductor : ℝ)
  fibre_finite : ∀ θ : T, {ψ : S | map ψ = θ}.Finite
  fibre_card : ∀ θ : T, Set.ncard {ψ : S | map ψ = θ} ≤ multiplicity

/-- Multiply finite-support characters after inflation to the union of supports. -/
def HorizontalCharacter.mulOnUnion {p : ℕ} [Fact p.Prime] {e : ℕ → ℕ}
    (χ ξ : HorizontalCharacter p e) : HorizontalCharacter p e where
  support := χ.support ∪ ξ.support
  toMonoidHom :=
    (χ.toMonoidHom.comp (horizontalRestrictionHom Finset.subset_union_left)) *
    (ξ.toMonoidHom.comp (horizontalRestrictionHom Finset.subset_union_right))

def HorizontalCharacter.powerOnSupport {p : ℕ} [Fact p.Prime] {e : ℕ → ℕ}
    (χ : HorizontalCharacter p e) (a : ℕ) : HorizontalCharacter p e where
  support := χ.support
  toMonoidHom := χ.toMonoidHom ^ a

/-- Exact-order finite-correction conclusion. Disjointness from A prevents a
correction from cancelling the character's p^m-order component. The exponent
a is prime to p, an essential strengthening of mere nontriviality. -/
def HorizontalMeasure.HasFiniteCorrection {p : ℕ} [Fact p.Prime]
    {e : ℕ → ℕ} {R : Subring ℂ_[p]} (μ : HorizontalMeasure R p e)
    (m : ℕ) (A : Finset ℕ) : Prop :=
  ∀ χ : HorizontalCharacter p e,
    orderOf χ.toMonoidHom = p ^ m → Disjoint χ.support A →
    ∃ a : ℕ, a < p ^ m ∧ Nat.Coprime a p ∧
      ∃ ξ : HorizontalCharacter p e, ξ.support ⊆ A ∧
        orderOf ξ.toMonoidHom ∣ p ^ m ∧
        μ.eval ((χ.powerOnSupport a).mulOnUnion ξ) ≠ 0

/-- The one-prime-power induction step, with freely chosen conductor avoidance. -/
def HasPrimePowerPropagation {N k : ℕ} (ι : MTT.Qbar →+* ℂ)
    (f : MTT.Eigenform N k ι) : Prop :=
  ∀ (η : DirichletCharacterWithLevel), η.2.IsPrimitive → η.2 (-1) = 1 →
    ∀ (p m B : ℕ) [Fact p.Prime], p ≠ 2 → 0 < m → 0 < B →
      2 ≤ orderOf η.2 → Nat.Coprime (orderOf η.2) p →
      Nat.Coprime (N * p) η.2.conductor →
      @MTT.criticalLValue ι f.form η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2
        (k / 2 - 1) ≠ 0 →
      ∃ α : ℝ, 0 < α ∧
        HasLogPowerLowerBound (seededPrimePowerNonvanishingCount ι f η p m B) α

/-- Elementary arithmetic needed when replacing a seed by its primitive product.
These are conclusions to prove, not additional mission hypotheses. -/
structure PrimitiveProductArithmetic : Prop where
  primitive : ∀ η ψ : DirichletCharacterWithLevel,
    (primitiveProductV2 η ψ).2.IsPrimitive
  conductor : ∀ η ψ : DirichletCharacterWithLevel,
    η.2.IsPrimitive → ψ.2.IsPrimitive →
    Nat.Coprime η.2.conductor ψ.2.conductor →
    (primitiveProductV2 η ψ).2.conductor = η.2.conductor * ψ.2.conductor
  order : ∀ η ψ : DirichletCharacterWithLevel,
    η.2.IsPrimitive → ψ.2.IsPrimitive →
    Nat.Coprime η.2.conductor ψ.2.conductor →
    Nat.Coprime (orderOf η.2) (orderOf ψ.2) →
    orderOf (primitiveProductV2 η ψ).2 = orderOf η.2 * orderOf ψ.2
  even : ∀ η ψ : DirichletCharacterWithLevel,
    η.2 (-1) = 1 → ψ.2 (-1) = 1 → (primitiveProductV2 η ψ).2 (-1) = 1
  injective : ∀ η : DirichletCharacterWithLevel, η.2.IsPrimitive →
    Function.Injective (fun ψ : {ψ : DirichletCharacterWithLevel |
      ψ.2.IsPrimitive ∧ Nat.Coprime η.2.conductor ψ.2.conductor} =>
        primitiveProductV2 η ψ.val)

end HorizontalPadicL


