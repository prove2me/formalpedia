-- Prove2me | Definitions.Def_AsymptoticallyMinimalLittlewood
-- name    : AsymptoticallyMinimalLittlewood
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:00.490092+00:00
-- url     : https://prove2.me/theorems/bd37e43a-f1af-41a6-8b23-ac1d3dc8eab5
-- statement:
--   For a nonnegative integer N and real coefficients ε₀, …, εₙ₋₁, littlewoodValue(ε,z) is the complex polynomial ∑ₖ₌₀ᴺ⁻¹ εₖzᵏ. The predicate IsRealSigning means that every coefficient equals either −1 or 1. MainStatement is the defined proposition that, for every real η > 0, there exists an integer N₀ ≥ 1 such that, for every integer N ≥ N₀, one can choose N coefficients from {−1,1} for which |∑ₖ₌₀ᴺ⁻¹ εₖzᵏ| ≤ (1 + η)√N holds for every complex z with |z| = 1. Thus the coefficient choice may depend on N and η, while its bound holds uniformly on the entire unit circle.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/AsymptoticallyMinimalLittlewood.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/AsymptoticallyMinimalLittlewood.lean; bytes 16..536
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace AsymptoticallyMinimalLittlewood

def littlewoodValue {N : ℕ} (ε : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)

def IsRealSigning {N : ℕ} (ε : Fin N → ℝ) : Prop :=
  ∀ k, ε k = -1 ∨ ε k = 1

def MainStatement : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖littlewoodValue ε z‖ ≤ (1 + η) * Real.sqrt N



end AsymptoticallyMinimalLittlewood
end OAI


