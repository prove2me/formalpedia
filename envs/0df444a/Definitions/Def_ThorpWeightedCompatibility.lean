-- Prove2me | Definitions.Def_ThorpWeightedCompatibility
-- name    : ThorpWeightedCompatibility
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:29.911992+00:00
-- url     : https://prove2.me/theorems/904a19cd-ae2b-4bee-aac1-ae0bbdb4e443
-- statement:
--   Rows(A,D) is the type of A-tuples of permutations of {0,…,D−1}, one permutation r_i per row index i, and Cols(A,D) is the type of D-tuples of permutations of {0,…,A−1}, one permutation c_j per column index j. A pair (r,c) is Compatible if for every j<D the map i ↦ c_{r_i(j)}(i) is injective on {0,…,A−1}. uniformMean(f) is the arithmetic average of a real function over a finite type. For θ and a weight function w on a finite type, marginalFactor(θ,w) is (uniformMean of w(x)^(1/θ))^θ. Given nonnegative-valued or arbitrary real weights w_i(σ) for each row i and permutation σ of Fin D, and v_k(τ) for each column k and permutation τ of Fin A, weightedCompatibility(A,D,w,v) equals (AD)!/((D!)^A (A!)^D) times the uniform average, over all pairs (r,c) in Rows×Cols, of the quantity ∏_i w_i(r_i)·∏_k v_k(c_k) when (r,c) is compatible and 0 otherwise. WeightedCompatibilityTheorem is a defined proposition, not an established theorem. It asserts that there exist positive reals L, C₀ and m₀ such that, for all natural numbers A and D, writing n=AD, m=√n and θ=1−L/log m, whenever m≥m₀, θ>0, m/2≤A≤2m and m/2≤D≤2m, every choice of nonnegative weights w and v satisfies weightedCompatibility(A,D,w,v) ≤ exp(C₀·n^(54/100)) · ∏_i marginalFactor(θ,w_i) · ∏_k marginalFactor(θ,v_k).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThorpWeightedCompatibility.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThorpWeightedCompatibility.lean; bytes 16..1769
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

abbrev Rows (A D : ℕ) := Fin A → Equiv.Perm (Fin D)
abbrev Cols (A D : ℕ) := Fin D → Equiv.Perm (Fin A)

def Compatible {A D : ℕ} (r : Rows A D) (c : Cols A D) : Prop :=
  ∀ j : Fin D, Function.Injective (fun i : Fin A => c (r i j) i)

noncomputable def uniformMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

noncomputable def marginalFactor {α : Type*} [Fintype α]
    (θ : ℝ) (w : α → ℝ) : ℝ :=
  (uniformMean (fun x => Real.rpow (w x) (1 / θ))) ^ θ

noncomputable def weightedCompatibility (A D : ℕ)
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ) : ℝ := by
  classical
  exact (Nat.factorial (A * D) : ℝ) /
    ((Nat.factorial D : ℝ) ^ A * (Nat.factorial A : ℝ) ^ D) *
    uniformMean (fun rc : Rows A D × Cols A D =>
      if Compatible rc.1 rc.2 then (∏ i, w i (rc.1 i)) * (∏ k, v k (rc.2 k)) else 0)

def WeightedCompatibilityTheorem : Prop :=
  ∃ L C₀ m₀ : ℝ, 0 < L ∧ 0 < C₀ ∧ 0 < m₀ ∧
    ∀ A D : ℕ,
    let n : ℝ := A * D
    let m := Real.sqrt n
    let θ := 1 - L / Real.log m
    m₀ ≤ m → 0 < θ → m / ((2 : ℕ) : ℝ) ≤ A → (A : ℝ) ≤ ((2 : ℕ) : ℝ) * m →
    m / ((2 : ℕ) : ℝ) ≤ D → (D : ℝ) ≤ ((2 : ℕ) : ℝ) * m →
    ∀ (w : Fin A → Equiv.Perm (Fin D) → ℝ)
      (v : Fin D → Equiv.Perm (Fin A) → ℝ),
    (∀ i σ, 0 ≤ w i σ) → (∀ k σ, 0 ≤ v k σ) →
    weightedCompatibility A D w v ≤
      Real.exp (C₀ * n ^ (((54 : ℕ) : ℝ) / ((100 : ℕ) : ℝ))) *
        (∏ i, marginalFactor θ (w i)) * (∏ k, marginalFactor θ (v k))




end ThorpCompatibility
end OAI


