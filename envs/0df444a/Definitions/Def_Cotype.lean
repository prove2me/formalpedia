-- Prove2me | Definitions.Def_Cotype
-- name    : Cotype
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:05.617067+00:00
-- url     : https://prove2.me/theorems/92f0cb8c-189a-4bbe-a733-dd4e09c706ce
-- statement:
--   For a real normed vector space E, Cube(n) is the set of Boolean vectors of length n, with sign(false)=1 and sign(true)=−1. The average of a function on a finite set is its sum multiplied by the reciprocal of the set’s cardinality. For f:Cube(n)→E, its cube L² norm is the square root of the average of ‖f(ε)‖². Given vectors x₀,…,xₙ₋₁, their Rademacher sum at ε is ∑ᵢ sign(εᵢ)xᵢ. The ith moment of f is the average of sign(εᵢ)f(ε), and its Rademacher projection is the Rademacher sum of these moments. K-convexity means that some constant K≥0 bounds the cube L² norm of this projection by K times that of f, uniformly over every n and f. E has cotype q if q≥2 and there is C≥0 such that (∑ᵢ ‖xᵢ‖^q)^(1/q)≤C times the cube L² norm of the Rademacher sum, for every n and every family of n vectors. Finite cotype means having cotype q for some real q. The approximation property means that, for every compact subset M and every δ>0, there is a continuous linear operator S:E→E with finite-dimensional range satisfying ‖Sx−x‖<δ for all x∈M. For complete, nontrivial E, MainTarget is the defined proposition that the approximation property implies that E is K-convex if and only if both E and its continuous real dual have finite cotype.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Cotype.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Cotype.lean; bytes 16..1649
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators
universe u v

namespace Cotype

abbrev Cube (n : ℕ) := Fin n → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

def average {ι : Type u} [Fintype ι] {E : Type v} [AddCommMonoid E] [Module ℝ E]
    (f : ι → E) : E := (Fintype.card ι : ℝ)⁻¹ • ∑ i, f i

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

def cubeL2 {n : ℕ} (f : Cube n → E) : ℝ :=
  Real.sqrt (average (fun ε => ‖f ε‖ ^ 2))

def rademacherSum {n : ℕ} (x : Fin n → E) (ε : Cube n) : E :=
  ∑ i, sign (ε i) • x i

def moment {n : ℕ} (f : Cube n → E) (i : Fin n) : E :=
  average (fun ε => sign (ε i) • f ε)

def radProjection {n : ℕ} (f : Cube n → E) : Cube n → E :=
  rademacherSum E (moment E f)

def KConvex : Prop := ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (f : Cube n → E),
  cubeL2 E (radProjection E f) ≤ K * cubeL2 E f

def HasCotype (q : ℝ) : Prop := 2 ≤ q ∧ ∃ C : ℝ, 0 ≤ C ∧
  ∀ (n : ℕ) (x : Fin n → E),
    (∑ i, ‖x i‖ ^ q) ^ (1 / q) ≤ C * cubeL2 E (rademacherSum E x)

def FiniteCotype : Prop := ∃ q : ℝ, HasCotype E q

def ApproximationProperty : Prop := ∀ (M : Set E), IsCompact M →
  ∀ δ : ℝ, 0 < δ → ∃ S : E →L[ℝ] E,
    FiniteDimensional ℝ (LinearMap.range S.toLinearMap) ∧
    ∀ x ∈ M, ‖S x - x‖ < δ

def MainTarget [CompleteSpace E] [Nontrivial E] : Prop :=
  ApproximationProperty E →
    (KConvex E ↔ FiniteCotype E ∧ FiniteCotype (E →L[ℝ] ℝ))

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]



end Cotype
end
end OAI


