-- Prove2me | Definitions.Def_BallPacking
-- name    : BallPacking
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:01.071893+00:00
-- url     : https://prove2.me/theorems/ee62d843-f18a-436c-87ec-4b2ca1c483d9
-- statement:
--   For a nonnegative integer n, Phase(n) is ℂⁿ, and the capacity of z is π∑ⱼ|zⱼ|². The closed and open balls with parameter r consist of points with capacity at most r and strictly less than r, respectively; thus r is a capacity parameter rather than a Euclidean radius. The standard real symplectic form is ω(u,v)=∑ⱼ(Re(uⱼ)Im(vⱼ)−Im(uⱼ)Re(vⱼ)). A map f:ℂⁿ→ℂⁿ is SymplecticOn a set U when U is open, f is infinitely differentiable over ℝ on U, its restriction to U is a topological embedding, and its real derivative preserves ω at every point of U: ω(Dfₓu,Dfₓv)=ω(u,v) for all tangent vectors u,v. HasPacking(n,k,R,r) means that, for each of k ball capacities rᵢ, there is an open neighborhood Uᵢ of the corresponding closed ball and a map symplectic on Uᵢ whose image of that closed ball lies in the open ball of capacity R, with these k images pairwise disjoint. PackingInequalities(n,k,R,r) is the conjunction ∑ᵢrᵢⁿ<Rⁿ and rᵢ+rⱼ<R for every distinct pair of indices. These predicates impose no positivity assumptions on the real capacities and assert no equivalence between packing existence and the inequalities.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BallPacking.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BallPacking.lean; bytes 16..1310
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


