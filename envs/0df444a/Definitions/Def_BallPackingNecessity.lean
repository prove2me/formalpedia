-- Prove2me | Definitions.Def_BallPackingNecessity
-- name    : BallPackingNecessity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:01.136921+00:00
-- url     : https://prove2.me/theorems/35913817-c72b-4e45-9b1b-d9ff8671be13
-- statement:
--   For nonnegative integers n and k, the phase space is ℂⁿ, represented by n complex coordinates, and the capacity of z is π times the sum of the squared absolute values of its coordinates. The closed and open balls with capacity parameter r consist respectively of points with capacity at most r and less than r; r is thus a capacity parameter rather than a Euclidean radius. The standard symplectic form is ω(u,v)=∑ⱼ(Re(uⱼ)Im(vⱼ)−Im(uⱼ)Re(vⱼ)). A map is SymplecticOn a set U when U is open, the map is infinitely differentiable over ℝ on U, its restriction to U is a topological embedding, and its derivative at every point of U preserves ω. HasPacking(n,k,R,r) is the proposition that each of the k closed balls with capacity parameters rᵢ admits such a map on an open neighborhood containing it, with its image contained in the open ball of capacity R, and that these k closed-ball images are pairwise disjoint. PackingInequalities(n,k,R,r) separately means ∑ᵢrᵢⁿ<Rⁿ and rᵢ+rⱼ<R for every pair of distinct indices. Neither proposition assumes positivity of R or the rᵢ, and this block does not assert an implication between the packing proposition and the inequalities.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BallPackingNecessity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BallPackingNecessity.lean; bytes 16..1314
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

abbrev Phase (n : ℕ) := Fin n → ℂ

noncomputable def capacity {n : ℕ} (z : Phase n) : ℝ :=
  Real.pi * ∑ j, Complex.normSq (z j)

def closedBall (n : ℕ) (r : ℝ) : Set (Phase n) := {z | capacity z ≤ r}

def openBall (n : ℕ) (r : ℝ) : Set (Phase n) := {z | capacity z < r}

noncomputable def standardForm {n : ℕ} (u v : Phase n) : ℝ :=
  ∑ j, ((u j).re * (v j).im - (u j).im * (v j).re)

 
def SymplecticOn {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ ∞ f U ∧
    Topology.IsEmbedding (fun x : U => f x) ∧
    ∀ x ∈ U, ∀ u v : Phase n,
      standardForm (fderiv ℝ f x u) (fderiv ℝ f x v) = standardForm u v

 
def HasPacking (n k : ℕ) (R : ℝ) (r : Fin k → ℝ) : Prop :=
  ∃ (U : Fin k → Set (Phase n)) (f : Fin k → Phase n → Phase n),
    (∀ i, closedBall n (r i) ⊆ U i ∧ SymplecticOn (U i) (f i) ∧
      Set.MapsTo (f i) (closedBall n (r i)) (openBall n R)) ∧
    (∀ i j, i ≠ j →
      Disjoint (f i '' closedBall n (r i)) (f j '' closedBall n (r j)))

def PackingInequalities (n k : ℕ) (R : ℝ) (r : Fin k → ℝ) : Prop :=
  (∑ i, r i ^ n) < R ^ n ∧ ∀ i j, i ≠ j → r i + r j < R



end HigherDimensionalBallPacking
end OAI


