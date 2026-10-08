-- Prove2me | Definitions.Def_ElementaryPositivity
-- name    : ElementaryPositivity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:09.677121+00:00
-- url     : https://prove2.me/theorems/2e6da283-ea4f-4c30-833c-7abdd905c5e2
-- statement:
--   For a nonnegative integer n, a natural unit interval graph is specified by a nondecreasing map h from {0, …, n−1} to itself satisfying i ≤ h(i). Distinct vertices i<j are adjacent exactly when j ≤ h(i). A permutation σ is a nondescent permutation when every adjacent decrease σ(i+1)<σ(i) occurs between adjacent graph vertices. Its graph inversion count inv_G(σ) is the number of pairs i<j for which σ(j)<σ(i) and σ(i), σ(j) are adjacent. A coloring f with r ordered colors is proper if adjacent vertices receive different colors; its ascent count asc_G(f) counts edges i<j with f(i)<f(j). The chromatic polynomial with ascent parameter q is the multivariate polynomial X_G(x;q)=Σ_f q^{asc_G(f)}∏_{i=0}^{n−1}x_{f(i)}, summed over proper r-colorings, with coefficients in ℕ[q]. A permutation witness consists of a map θ assigning an integer partition of n to every nondescent permutation, together with the requirement that, for every nonnegative integer r, X_G(x;q)=Σ_σ q^{inv_G(σ)}e_{θ(σ)}(x), summed over those permutations. Here e_λ is the product, over the parts of λ, of the corresponding elementary symmetric polynomials in the r color variables. This expansion is a required field of the witness; the definitions do not assert that such a witness exists for every graph.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ElementaryPositivity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ElementaryPositivity.lean; bytes 16..2024
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace ElementaryPositivity

structure NaturalUnitIntervalGraph (n : ℕ) where
  h : Fin n → Fin n
  increasing : Monotone h
  extensive : ∀ i, i ≤ h i

namespace NaturalUnitIntervalGraph

variable {n : ℕ} (G : NaturalUnitIntervalGraph n)

def Edge (i j : Fin n) : Prop :=
  (i < j ∧ j ≤ G.h i) ∨ (j < i ∧ i ≤ G.h j)

instance (i j : Fin n) : Decidable (G.Edge i j) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

def Nondescent (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val → σ j < σ i → G.Edge (σ i) (σ j)

instance (σ : Equiv.Perm (Fin n)) : Decidable (G.Nondescent σ) :=
  inferInstanceAs (Decidable (∀ i j : Fin n,
    i.val + 1 = j.val → σ j < σ i → G.Edge (σ i) (σ j)))

def graphInversions (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ σ ij.2 < σ ij.1 ∧ G.Edge (σ ij.1) (σ ij.2)).card

def Proper {r : ℕ} (f : Fin n → Fin r) : Prop :=
  ∀ i j : Fin n, G.Edge i j → f i ≠ f j

instance {r : ℕ} (f : Fin n → Fin r) : Decidable (G.Proper f) :=
  inferInstanceAs (Decidable (∀ i j : Fin n, G.Edge i j → f i ≠ f j))

def coloringAscents {r : ℕ} (f : Fin n → Fin r) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ G.Edge ij.1 ij.2 ∧ f ij.1 < f ij.2).card

noncomputable def chromatic (r : ℕ) : MvPolynomial (Fin r) (Polynomial ℕ) :=
  ∑ f ∈ Finset.univ.filter (G.Proper (r := r)),
    MvPolynomial.C (Polynomial.X ^ G.coloringAscents f) *
      ∏ i : Fin n, MvPolynomial.X (f i)

structure PermutationWitness where
  theta : {σ : Equiv.Perm (Fin n) // G.Nondescent σ} → Nat.Partition n
  expansion : ∀ r : ℕ, G.chromatic r =
    ∑ σ : {σ : Equiv.Perm (Fin n) // G.Nondescent σ},
      MvPolynomial.C (Polynomial.X ^ G.graphInversions σ.val) *
        MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (theta σ)

end NaturalUnitIntervalGraph
end ElementaryPositivity



end OAI


