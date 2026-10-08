-- Prove2me | Definitions.Def_EuclideanRamsey
-- name    : EuclideanRamsey
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:10.287037+00:00
-- url     : https://prove2.me/theorems/0a246569-731b-4336-a1a4-f118248ebf5d
-- statement:
--   For nonnegative integers s and d, a configuration a is an indexed family of s points in d-dimensional real Euclidean space, with no requirement that its points be distinct. Two configurations with the same number of indexed points, possibly in different dimensions, are congruent if every corresponding pairwise distance agrees. The defined proposition Ramsey(a) says that for every integer r ≥ 2 there is a dimension D ≥ 1 such that every coloring of D-dimensional Euclidean space with r colors contains a congruent indexed copy of a whose points all have one color. Let K be the smallest subfield of ℝ containing ℚ and every coordinate of a, and let T = K ⊗ℚ K. Each coordinate is regarded as an element of K, and each point is augmented by a constant coordinate: uᵢ,* = 1 and uᵢ,j = aᵢ,j for 0 ≤ j < d. The multiplication map μ: T → K is the ℚ-algebra homomorphism sending x ⊗ y to xy. FieldCriterion(a) is the proposition that there exists a matrix P over T, with rows and columns indexed by the extra coordinate * and the d spatial coordinates, such that for every point i, ∑α,β (uᵢ,α ⊗ 1)Pαβ(1 ⊗ uᵢ,β) = 0 in T, while μ(Pαβ) equals 1 when α = β and 0 otherwise for all spatial indices α and β.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EuclideanRamsey.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EuclideanRamsey.lean; bytes 16..1662
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def Congruent {s d D : ℕ} (a : Fin s → Space d) (b : Fin s → Space D) : Prop :=
  ∀ i j, dist (b i) (b j) = dist (a i) (a j)

def Ramsey {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ c : Space D → Fin r, ∃ b : Fin s → Space D,
      Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k

def coordinateField {s d : ℕ} (a : Fin s → Space d) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ (Set.range (fun ij : Fin s × Fin d => a ij.1 ij.2))

abbrev Coeff {s d : ℕ} (a : Fin s → Space d) := ↥(coordinateField a)
abbrev TensorRing {s d : ℕ} (a : Fin s → Space d) := Coeff a ⊗[ℚ] Coeff a

def coordinate {s d : ℕ} (a : Fin s → Space d) (i : Fin s) (j : Fin d) : Coeff a :=
  ⟨a i j, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self (i, j))⟩

def augmented {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : Option (Fin d) → Coeff a
  | none => 1
  | some j => coordinate a i j

def multiply {s d : ℕ} (a : Fin s → Space d) : TensorRing a →ₐ[ℚ] Coeff a :=
  Algebra.TensorProduct.lmul' ℚ

def FieldCriterion {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∃ P : Matrix (Option (Fin d)) (Option (Fin d)) (TensorRing a),
    (∀ i : Fin s, ∑ α, ∑ β,
      ((augmented a i α) ⊗ₜ[ℚ] (1 : Coeff a)) * P α β *
      ((1 : Coeff a) ⊗ₜ[ℚ] (augmented a i β)) = 0) ∧
    (∀ α β : Fin d, multiply a (P (some α) (some β)) = if α = β then 1 else 0)



end EuclideanRamsey
end
end OAI


