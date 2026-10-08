-- Prove2me | Definitions.Def_MarkovType
-- name    : MarkovType
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.077029+00:00
-- url     : https://prove2.me/theorems/a775f375-33e1-4503-bd27-9652ea0081c1
-- statement:
--   A finite reversible Markov chain on a finite state set S consists of a probability vector π and a row-stochastic nonnegative transition matrix P satisfying detailed balance π(s)P(s,t)=π(t)P(t,s). A state path of length n is a sequence ω₀,…,ω_n of n+1 states, and its weight is π(ω₀)·∏_{i<n} P(ω_i,ω_{i+1}). For a map f from S into a normed group X and an exponent p, stateCost(C,f,p,n) is the sum over all paths of length n of the path weight times ‖f(ω_n)−f(ω₀)‖^p, the p-th moment of the displacement of f after n steps from stationarity. MarkovTypeWith(p,K,X) is the defined proposition that p>0, K>0, and for every m, every finite reversible chain on Fin m, every f:Fin m→X and every n≥1, stateCost at time n is at most K^p·n times stateCost at time 1. HasMarkovType(p,X) says some constant K works, and HasNontrivialMarkovType(X) says HasMarkovType(p,X) holds for some p>1. For a real normed space X, an EquivalentNorm is a seminorm q with positive constants lower and upper such that lower·‖x‖≤q(x)≤upper·‖x‖ for all x. UniformConvex(q) means that for every ε in (0,2] there is δ>0 such that whenever q(x)≤1, q(y)≤1 and q(x−y)≥ε, the midpoint satisfies q((x+y)/2)≤1−δ. HasEquivalentUCNorm(X) says some equivalent norm on X is uniformly convex.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MarkovType.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MarkovType.lean; bytes 16..2126
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

structure FiniteReversibleChain (S : Type*) [Fintype S] where
  π : S → ℝ
  P : S → S → ℝ
  π_nonneg : ∀ s, 0 ≤ π s
  sum_π : ∑ s, π s = 1
  P_nonneg : ∀ s t, 0 ≤ P s t
  sum_P : ∀ s, ∑ t, P s t = 1
  balance : ∀ s t, π s * P s t = π t * P t s

abbrev StatePath (S : Type*) (n : ℕ) := Fin (n + 1) → S

def pathWeight {S : Type*} [Fintype S]
    (C : FiniteReversibleChain S) (n : ℕ) (ω : StatePath S n) : ℝ :=
  C.π (ω 0) * ∏ i : Fin n, C.P (ω i.castSucc) (ω i.succ)

def stateCost {S X : Type*} [Fintype S] [NormedAddCommGroup X]
    (C : FiniteReversibleChain S) (f : S → X) (p : ℝ) (n : ℕ) : ℝ :=
  ∑ ω : StatePath S n,
    pathWeight C n ω * Real.rpow (‖f (ω (Fin.last n)) - f (ω 0)‖) p

def MarkovTypeWith (p K : ℝ) (X : Type*) [NormedAddCommGroup X] : Prop :=
  0 < p ∧ 0 < K ∧
    ∀ (m : ℕ) (C : FiniteReversibleChain (Fin m)) (f : Fin m → X) (n : ℕ),
      1 ≤ n → stateCost C f p n ≤ Real.rpow K p * (n : ℝ) * stateCost C f p 1

def HasMarkovType (p : ℝ) (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∃ K : ℝ, MarkovTypeWith p K X

def HasNontrivialMarkovType (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∃ p : ℝ, 1 < p ∧ HasMarkovType p X

section

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

structure EquivalentNorm where
  p : Seminorm ℝ X
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  lower_bound : ∀ x, lower * ‖x‖ ≤ p x
  upper_bound : ∀ x, p x ≤ upper * ‖x‖

variable {X}

def UniformConvex (p : Seminorm ℝ X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 2 → ∃ δ : ℝ, 0 < δ ∧
    ∀ x y : X, p x ≤ 1 → p y ≤ 1 → ε ≤ p (x - y) →
      p ((1 / 2 : ℝ) • (x + y)) ≤ 1 - δ

def HasEquivalentUCNorm (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ N : EquivalentNorm X, UniformConvex N.p

end

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]



end MarkovSuperreflexivity
end
end OAI


