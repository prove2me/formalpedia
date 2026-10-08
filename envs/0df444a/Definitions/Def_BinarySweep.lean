-- Prove2me | Definitions.Def_BinarySweep
-- name    : BinarySweep
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:01.96299+00:00
-- url     : https://prove2.me/theorems/f0b41714-9b2c-434f-9b14-ab55008856fe
-- statement:
--   For a nonnegative integer d, the binary deck has positions {0,1}ᵈ. A coordinate layer chooses, separately for each assignment of the other d−1 coordinates, whether to flip coordinate j, giving independent switches on the edges parallel to j. A binary sweep applies these layers in increasing coordinate order. The finite law of a map from a finite set assigns each output its number of preimages divided by the size of the domain; applying this to all possible switch choices defines the law of one uniformly randomized binary sweep. The uniform law on a finite set assigns reciprocal-cardinality mass to each element, and total variation is half the sum of absolute mass differences. Representations act on D-dimensional complex Euclidean space; being unitary means preserving every vector norm. Their average operator under a real-valued weight p is ∑ₕ p(h)ρ(h). BinaryContractionTarget is the defined proposition that there exist a real γ > 0 and a threshold d₀ such that, for every d ≥ d₀, every nonnegative integer D, and every irreducible unitary representation ρ of the permutation group of the binary deck, the operator norm of its average under one sweep is at most D^(−γ). The real sign homomorphism assigns each permutation its sign as a real number. Convolution is (p*q)(h) = ∑ₓ p(x)q(x⁻¹h), with zeroth power the identity point mass; sweepLaw(d,t) is the t-fold convolution power of the one-sweep law. UniformSweepMixingTarget is the defined proposition that some fixed nonnegative integer w works as follows: for every ε > 0 there is d₀ such that, for all d ≥ d₀ and initial permutations τ, the law h ↦ sweepLaw(d,w)(hτ⁻¹) has total variation at most ε from the uniform law on all deck permutations.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BinarySweep.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BinarySweep.lean; bytes 16..3386
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace BinaryCoordinateSweeps

/-- The positions of a binary deck of dimension d. -/
abbrev Slot (d : ℕ) := Fin d → Bool

/-- Independent switches on the edges parallel to one coordinate. -/
def coordinateLayer (d : ℕ) (j : Fin d)
    (c : (({i : Fin d // i ≠ j} → Bool)) → Bool) : Equiv.Perm (Slot d) :=
  let e := Equiv.piSplitAt j (fun _ : Fin d => Bool)
  let sw : Equiv.Perm (Bool × ({i : Fin d // i ≠ j} → Bool)) :=
    { toFun := fun x => (x.1 ^^ c x.2, x.2)
      invFun := fun x => (x.1 ^^ c x.2, x.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  e.trans (sw.trans e.symm)

abbrev SweepCoins (d : ℕ) :=
  (j : Fin d) → ({i : Fin d // i ≠ j} → Bool) → Bool

/-- The coordinate layers are applied in increasing coordinate order. -/
def binarySweep (d : ℕ) (c : SweepCoins d) : Equiv.Perm (Slot d) :=
  (List.ofFn (fun j => coordinateLayer d j (c j))).reverse.prod

def finiteLaw {Ω G : Type*} [Fintype Ω] [Fintype G] (f : Ω → G) (g : G) : ℝ := by
  classical
  exact ∑ ω, if f ω = g then (Fintype.card Ω : ℝ)⁻¹ else 0

/-- Half the unnormalized sum of absolute probability-mass differences. -/
def totalVariation {G : Type*} [Fintype G] (p q : G → ℝ) : ℝ :=
  (1 / ((2 : ℕ) : ℝ)) * ∑ g, |p g - q g|

def uniformLaw (G : Type*) [Fintype G] : G → ℝ :=
  fun _ => (Fintype.card G : ℝ)⁻¹

def binaryLaw (d : ℕ) : Equiv.Perm (Slot d) → ℝ :=
  finiteLaw (binarySweep d)

abbrev RepSpace (D : ℕ) := EuclideanSpace ℂ (Fin D)

def IsUnitaryRep {G : Type*} [Monoid G]
    {D : ℕ} (ρ : Representation ℂ G (RepSpace D)) : Prop :=
  ∀ g x, ‖ρ g x‖ = ‖x‖

def averageOperator {G : Type*} [Fintype G] [Monoid G] {D : ℕ}
    (p : G → ℝ) (ρ : Representation ℂ G (RepSpace D)) :
    RepSpace D →L[ℂ] RepSpace D :=
  LinearMap.toContinuousLinearMap (∑ g, (p g : ℂ) • ρ g)

def BinaryContractionTarget : Prop :=
  ∃ g : ℝ, 0 < g ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ D : ℕ,
    ∀ ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D),
      ρ.IsIrreducible → IsUnitaryRep ρ →
      ‖averageOperator (binaryLaw d) ρ‖ ≤ (D : ℝ) ^ (-g)

def realSign {α : Type*} [Fintype α] [DecidableEq α] : Equiv.Perm α →* ℝ :=
  (Int.castRingHom ℝ).toMonoidHom.comp ((Units.coeHom ℤ).comp Equiv.Perm.sign)

section FiniteLaws
variable {G : Type*} [Fintype G] [Group G]

def convolution (p q : G → ℝ) (g : G) : ℝ := ∑ x, p x * q (x⁻¹ * g)

def pointMassOne (g : G) : ℝ := by
  classical
  exact if g = 1 then 1 else 0

/-- The law of independent repetitions, with the empty product at the identity. -/
def convolutionPower (p : G → ℝ) : ℕ → G → ℝ
  | 0 => pointMassOne
  | n + 1 => convolution p (convolutionPower p n)

end FiniteLaws

def sweepLaw (d t : ℕ) : Equiv.Perm (Slot d) → ℝ :=
  convolutionPower (binaryLaw d) t

/-- A single number of sweeps works uniformly over deterministic initial decks. -/
def UniformSweepMixingTarget : Prop :=
  ∃ w : ℕ, ∀ ε : ℝ, 0 < ε → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ τ : Equiv.Perm (Slot d),
      totalVariation (fun g => sweepLaw d w (g * τ⁻¹))
        (uniformLaw (Equiv.Perm (Slot d))) ≤ ε

end BinaryCoordinateSweeps
end

open scoped BigOperators



end OAI


