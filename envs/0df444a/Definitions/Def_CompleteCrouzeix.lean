-- Prove2me | Definitions.Def_CompleteCrouzeix
-- name    : CompleteCrouzeix
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:04.727178+00:00
-- url     : https://prove2.me/theorems/71f7195f-1c0b-4c23-b2f4-ee69839e3855
-- statement:
--   For a complex n × n matrix A, its numerical range is the set of all values ⟨x, Ax⟩ obtained from vectors x in complex Euclidean n-space with norm one. Given complex m × m coefficient matrices B₀, …, B_d, polynomialValue at a complex scalar z is the matrix polynomial P(z) = ∑ₖ₌₀ᵈ zᵏBₖ. Its evaluation at A is defined on the tensor product of the two coordinate spaces by polynomialAt(A,B) = ∑ₖ₌₀ᵈ Aᵏ ⊗ Bₖ, an nm × nm matrix, where ⊗ denotes the Kronecker product. The quantity rangeMaximum(A,B) is the supremum of ‖P(z)‖ over z in the numerical range of A, with all matrix norms taken to be the Euclidean operator norm. For a real constant C, UniversalBound(C) is the proposition that ‖∑ₖ₌₀ᵈ Aᵏ ⊗ Bₖ‖ ≤ C rangeMaximum(A,B) for every pair of positive integers n and m, every nonnegative integer d, and every choice of A and the coefficient matrices B₀, …, B_d. No particular value of C is asserted to satisfy this proposition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CompleteCrouzeix.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CompleteCrouzeix.lean; bytes 16..1189
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace CompleteCrouzeix

def numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    inner ℂ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x) = z}

def polynomialValue {m d : ℕ} (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ)
    (z : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ∑ k : Fin (d + 1), (z ^ (k : ℕ)) • B k

def polynomialAt {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  ∑ k : Fin (d + 1), Matrix.kronecker (A ^ (k : ℕ)) (B k)

def rangeMaximum {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  sSup ((fun z => ‖polynomialValue B z‖) '' numericalRange A)

def UniversalBound (C : ℝ) : Prop :=
  ∀ (n m d : ℕ), 0 < n → 0 < m →
    ∀ (A : Matrix (Fin n) (Fin n) ℂ)
      (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ),
      ‖polynomialAt A B‖ ≤ C * rangeMaximum A B



end CompleteCrouzeix
end
end OAI


