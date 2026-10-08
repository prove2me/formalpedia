-- Prove2me | Definitions.Def_GaussianMoat
-- name    : GaussianMoat
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:12.821287+00:00
-- url     : https://prove2.me/theorems/57ce354b-0a04-46fd-8968-49d4348991d3
-- statement:
--   PrimeVertex is the type of Gaussian primes, namely irreducible elements of the Gaussian integers ℤ[i]. For a real distance bound D, primeGraph(D) is the simple graph on these primes in which two distinct primes p and q are adjacent exactly when their Euclidean distance in the complex plane is at most D, and component(D,p) is the set of primes reachable from p in this graph, that is, the connected component of p. MainEndpoint is the defined proposition (not an established theorem) that no Gaussian-moat walk to infinity exists: for every real D, there is no injective sequence z of Gaussian primes indexed by the natural numbers whose consecutive terms satisfy |z(t+1) − z(t)| ≤ D. UniformEndpoint is the stronger defined proposition that for every real D there is a natural number B such that every component(D,p) is finite with at most B elements, and every injective finite chain of n Gaussian primes z₀,…,z_{n−1} with consecutive distances at most D has length n ≤ B.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianMoat.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianMoat.lean; bytes 16..1073
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace GaussianMoat

abbrev PrimeVertex := {z : GaussianInt // Irreducible z}

noncomputable def primeGraph (D : ℝ) : SimpleGraph PrimeVertex where
  Adj p q := p ≠ q ∧ dist (p.val : ℂ) (q.val : ℂ) ≤ D
  symm := by
    constructor
    intro p q h
    exact ⟨h.1.symm, by simpa only [dist_comm] using h.2⟩
  loopless := by
    constructor
    intro p h
    exact h.1 rfl

def component (D : ℝ) (p : PrimeVertex) : Set PrimeVertex :=
  {q | (primeGraph D).Reachable p q}

def MainEndpoint : Prop :=
  ∀ (D : ℝ) (z : ℕ → GaussianInt),
    (∀ t, Irreducible (z t)) → Function.Injective z →
    (∀ t, dist (z (t + 1) : ℂ) (z t : ℂ) ≤ D) → False

def UniformEndpoint : Prop :=
  ∀ D : ℝ, ∃ B : ℕ,
    (∀ p : PrimeVertex, (component D p).Finite ∧ (component D p).ncard ≤ B) ∧
    (∀ (n : ℕ) (z : Fin n → GaussianInt),
      (∀ i, Irreducible (z i)) → Function.Injective z →
      (∀ i j : Fin n, j.val = i.val + 1 → dist (z j : ℂ) (z i : ℂ) ≤ D) →
      n ≤ B)



end GaussianMoat
end OAI


