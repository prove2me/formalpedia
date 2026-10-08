-- Prove2me | Definitions.Def_TalagrandDiscreteConvexity
-- name    : TalagrandDiscreteConvexity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:28.681715+00:00
-- url     : https://prove2.me/theorems/a3df7bb9-701a-49fe-8eb4-bba875df3f2d
-- statement:
--   For a finite type α with decidable equality, a Family is a finite set of finite subsets of α. For p real, bernoulliMass(p,s) is p^|s|(1−p)^|α∖s|, the product-Bernoulli mass of the subset s with each coordinate present independently with parameter p, and familyMeasure(p,D) is the sum of these masses over the members of an arbitrary family D, with no monotonicity assumed. The cost of a family G of generators is the sum over I in G of p^|I|, so each distinct generator is charged once. Covers(G,A) means every set S in A contains some generator I in G as a subset. Small(p,A) means there exists a family G that covers A and has cost at most 1/2. For k a natural number and a k-tuple f of subsets, unionTuple(f) is the union of its k entries, with no distinctness or disjointness required. Finally exceptional(k,D) is the family of all subsets S of α such that no choice of k members of D (repetitions allowed) has a union containing S. These are definitions only, and no theorem relating them is stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TalagrandDiscreteConvexity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TalagrandDiscreteConvexity.lean; bytes 158..1583
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

abbrev Family (α : Type*) := Finset (Finset α)

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

/-- Independent Bernoulli coordinates, including every absent coordinate. -/
def bernoulliMass (p : ℝ) (s : Finset α) : ℝ :=
  p ^ s.card * (1 - p) ^ (Finset.univ \ s).card

/-- The probability of an arbitrary family, with no monotonicity condition. -/
def familyMeasure (p : ℝ) (D : Family α) : ℝ :=
  ∑ s ∈ D, bernoulliMass p s

/-- Each distinct generator is charged once at the original density. -/
def cost (p : ℝ) (G : Family α) : ℝ := ∑ I ∈ G, p ^ I.card

/-- Every covered set contains a generator. -/
def Covers (G A : Family α) : Prop := ∀ S ∈ A, ∃ I ∈ G, I ⊆ S

/-- An actual finite containment cover with total cost at most one half. -/
def Small (p : ℝ) (A : Family α) : Prop :=
  ∃ G : Family α, Covers G A ∧ cost p G ≤ 1 / 2

/-- Exactly `k` entries, with no distinctness or disjointness restriction. -/
def unionTuple {k : ℕ} (f : Fin k → Finset α) : Finset α :=
  Finset.univ.biUnion f

/-- All subsets contained in no union of `k` members of the given family. -/
def exceptional (k : ℕ) (D : Family α) : Family α := by
  classical
  exact Finset.univ.filter (fun S =>
    ∀ f : Fin k → Finset α, (∀ j, f j ∈ D) → ¬ S ⊆ unionTuple f)



end
end TalagrandDiscreteConvexity
end OAI


