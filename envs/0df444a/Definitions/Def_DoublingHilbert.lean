-- Prove2me | Definitions.Def_DoublingHilbert
-- name    : DoublingHilbert
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:08.470556+00:00
-- url     : https://prove2.me/theorems/5782a4bd-fded-4e02-82a3-ac232d238d02
-- statement:
--   RealL2 is the real Hilbert space ℓ²(ℕ) of square-summable real sequences. For a subset S of this space and a nonnegative integer bound, DoublingAtMost(S,bound) means that every intrinsic open ball in S centered at x∈S with radius r>0 can be covered by at most bound intrinsic open balls of radius r/2 whose centers also lie in S. Explicitly, there is a finite set of such centers so that each y∈S with dist(y,x)<r has distance less than r/2 from one of them. For a nonnegative integer k, AdmitsBiLipschitzEmbedding(S,k) means that there exist a map f from S into k-dimensional real Euclidean space, a scale a>0, and a finite real distortion D≥1 such that a·dist(x,y)≤dist(f(x),f(y))≤D·a·dist(x,y) for all x,y∈S. These inequalities in particular make f injective and allow an arbitrary positive overall rescaling.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DoublingHilbert.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DoublingHilbert.lean; bytes 16..759
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace DoublingHilbert

abbrev RealL2 := lp (fun _ : ℕ => ℝ) 2

/-- Intrinsic open-ball doubling with a specified integer bound and centers in the subset. -/
def DoublingAtMost (S : Set RealL2) (bound : ℕ) : Prop :=
  ∀ x : S, ∀ r : ℝ, 0 < r →
    ∃ centers : Finset S, centers.card ≤ bound ∧
      ∀ y : S, dist y x < r → ∃ c ∈ centers, dist y c < r / 2

/-- Finite distortion includes an arbitrary positive change of scale. -/
def AdmitsBiLipschitzEmbedding (S : Set RealL2) (k : ℕ) : Prop :=
  ∃ f : S → EuclideanSpace ℝ (Fin k),
    ∃ a : ℝ, 0 < a ∧ ∃ D : ℝ, 1 ≤ D ∧
      ∀ x y : S, a * dist x y ≤ dist (f x) (f y) ∧
        dist (f x) (f y) ≤ D * a * dist x y



end DoublingHilbert
end OAI


