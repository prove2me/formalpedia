-- Prove2me | Definitions.Def_SymmetricMahlerEquality
-- name    : SymmetricMahlerEquality
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:28.082269+00:00
-- url     : https://prove2.me/theorems/714e80e4-c39f-46c5-b558-656e4c6bf42a
-- statement:
--   For a finite index type I, coordinatePolar(K) of a set K of functions I → ℝ is the set of all p such that the pairing ∑ᵢ p(i)v(i) is at most 1 for every v in K. For sets A ⊆ ℝᵏ and B ⊆ ℝˡ (points as functions on Fin k and Fin l), hannerProduct(A,B) is the set of points in ℝ^(k+l) obtained by appending a point y of B to a point x of A, that is, the Cartesian product A × B embedded in ℝ^(k+l). hannerJoin(A,B) is the convex hull in ℝ^(k+l) of the union of the images of A under x ↦ (x,0) and of B under y ↦ (0,y). IsHanner is an inductively defined predicate on subsets of ℝⁿ for varying n: for every a>0 the symmetric interval [−a,a] in ℝ¹ is Hanner, and if A and B are Hanner then so are hannerProduct(A,B) and hannerJoin(A,B). IsLinearHanner(K) says that a subset K of ℝⁿ is the image of some Hanner set H ⊆ ℝⁿ under an invertible linear map of ℝⁿ onto itself. These are definitions only, with no theorem asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SymmetricMahlerEquality.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SymmetricMahlerEquality.lean; bytes 16..1353
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace SymmetricMahler

section

open Real Complex Set Finset
variable {I : Type*} [Fintype I]

def coordinatePolar (K : Set (I → ℝ)) : Set (I → ℝ) :=
  {p | ∀ v ∈ K, (∑ i, p i*v i) ≤ 1}

end

noncomputable section

open Set MeasureTheory Metric

def hannerProduct {k l : ℕ} (A : Set (Fin k → ℝ)) (B : Set (Fin l → ℝ)) :
    Set (Fin (k + l) → ℝ) :=
  {z | ∃ x ∈ A, ∃ y ∈ B, z = Fin.append x y}

def hannerJoin {k l : ℕ} (A : Set (Fin k → ℝ)) (B : Set (Fin l → ℝ)) :
    Set (Fin (k + l) → ℝ) :=
  convexHull ℝ
    (((fun x : Fin k → ℝ => Fin.append x 0) '' A) ∪
      ((fun y : Fin l → ℝ => Fin.append 0 y) '' B))

inductive IsHanner : {n : ℕ} → Set (Fin n → ℝ) → Prop
  | interval (a : ℝ) (ha : 0 < a) :
      IsHanner (Icc (fun _ : Fin 1 => -a) (fun _ : Fin 1 => a))
  | product {k l : ℕ} {A : Set (Fin k → ℝ)} {B : Set (Fin l → ℝ)}
      (hA : IsHanner A) (hB : IsHanner B) : IsHanner (hannerProduct A B)
  | join {k l : ℕ} {A : Set (Fin k → ℝ)} {B : Set (Fin l → ℝ)}
      (hA : IsHanner A) (hB : IsHanner B) : IsHanner (hannerJoin A B)

def IsLinearHanner {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  ∃ H : Set (Fin n → ℝ), IsHanner H ∧
    ∃ T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ), K = T '' H



end
end SymmetricMahler
end OAI


