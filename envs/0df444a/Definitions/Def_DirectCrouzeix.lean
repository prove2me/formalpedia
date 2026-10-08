-- Prove2me | Definitions.Def_DirectCrouzeix
-- name    : DirectCrouzeix
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:07.846172+00:00
-- url     : https://prove2.me/theorems/1069382e-6dd0-4b71-8d32-1845df67bfb9
-- statement:
--   For an n×n complex matrix A, its numerical range is W(A) = {⟨u, Au⟩ : u ∈ ℂⁿ and ‖u‖₂ = 1}. Given a nonnegative integer d and m×m complex coefficient matrices B₀, …, B_d, the matrix-valued polynomial is P(z) = ∑ₖ₌₀ᵈ zᵏBₖ. Its tensor evaluation at A is ∑ₖ₌₀ᵈ Aᵏ ⊗ Bₖ, an nm×nm matrix formed using Kronecker products. The range maximum is defined as the real supremum of ‖P(z)‖ over z ∈ W(A), with matrix norms taken to be the operator norms induced by Euclidean norms. For a real constant c, UniversalBound(c) is the proposition that, for every positive n and m, every nonnegative d, every such matrix A, and every such coefficient family, ‖∑ₖ₌₀ᵈ Aᵏ ⊗ Bₖ‖ ≤ c sup_{z∈W(A)} ‖P(z)‖. This defines the universal bound property without asserting that any particular c satisfies it.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DirectCrouzeix.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DirectCrouzeix.lean; bytes 16..1175
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

def numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ u : EuclideanSpace ℂ (Fin n), ‖u‖ = 1 ∧
    inner ℂ u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u) = z}

def polynomialValue {m d : ℕ} (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ)
    (z : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ∑ k : Fin (d + 1), z ^ (k : ℕ) • B k

def tensorEvaluation {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  ∑ k : Fin (d + 1), (A ^ (k : ℕ)) ⊗ₖ (B k)

def rangeMaximum {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  sSup ((fun z => ‖polynomialValue B z‖) '' numericalRange A)

def UniversalBound (c : ℝ) : Prop :=
  ∀ (n m d : ℕ), 0 < n → 0 < m →
    ∀ (A : Matrix (Fin n) (Fin n) ℂ)
      (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ),
      ‖tensorEvaluation A B‖ ≤ c * rangeMaximum A B



end DirectCrouzeix
end
end OAI


