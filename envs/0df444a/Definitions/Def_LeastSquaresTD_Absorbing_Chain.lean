-- Prove2me | Definitions.Def_LeastSquaresTD_Absorbing_Chain
-- name    : LeastSquaresTD_Absorbing_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:15:03.962698+00:00
-- url     : https://prove2.me/theorems/bb508012-b3bb-4302-98d8-b86fbebde00d
-- title:
--   Finite Markov chain, absorbing states, expected reward and value
-- statement:
--   Fix a policy in a finite-state Markov decision process. The induced **Markov chain** has a finite, nonempty state space $X$ and a row-stochastic transition matrix $P$. A transition from $x$ to $y$ earns a deterministic real reward $R(x,y)$, and $\gamma$ is the discount factor.
--
--   An **absorbing state** satisfies $P(x,x)=1$; write $\mathcal T$ for these states and $\mathcal N=X\setminus\mathcal T$. The chain is absorbing if an absorbing state can be reached with positive probability from every state. A start distribution $S$ has no inaccessible states if every state can be reached from a state with positive $S$-probability. The expected immediate reward and value function are
--
--   $$
--   \bar r(x)=\sum_{y\in X}P(x,y)R(x,y),\qquad V(x)=\sum_{k=0}^{\infty}\gamma^k(P^k\bar r)(x).
--   $$
--
--   These are the chain and return used throughout the mission. The value is defined by expected returns, so the summability needed at $\gamma=1$ remains a theorem claim. The restart kernel follows $P$ from a non-absorbing state and draws a new start state from $S$ after an absorbing state is reached.
--
--   **Formalization Note** The paper leaves “absorbing” to Kemeny and Snell and does not define “inaccessible”; these are read as reachability of an absorbing state from every state and reachability from the support of $S$, respectively. The fixed-policy setting removes the action argument, as on p. 35.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), https://doi.org/10.1023/A:1018056104778, pp. 34–35, §2 and Table 1; pp. 42–43, Figure 2 and Theorem 1

import Mathlib

namespace LeastSquaresTD.Absorbing

/-- The finite, row-stochastic transition matrix used after fixing a policy (§2, p. 35). -/
structure Chain (X : Type*) [Fintype X] where
  P : Matrix X X ℝ
  nonneg : ∀ x y, 0 ≤ P x y
  row_sum : ∀ x, ∑ y, P x y = 1

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Kemeny–Snell's absorbing condition as used in Theorem 1: an absorbing state is
reachable from every state. The absorbing states are those with `P(x,x)=1`. -/
def Chain.IsAbsorbing (C : Chain X) : Prop :=
  ∀ x, ∃ (n : ℕ) (y : X), C.P y y = 1 ∧ 0 < (C.P ^ n) x y

/-- The non-absorbing states, denoted `𝒩` in Theorem 1. -/
def Chain.Nonabsorbing (C : Chain X) : Type _ := {x : X // C.P x x ≠ 1}

noncomputable instance (C : Chain X) : Fintype C.Nonabsorbing := by
  classical
  unfold Chain.Nonabsorbing
  infer_instance

noncomputable instance (C : Chain X) : DecidableEq C.Nonabsorbing := Classical.decEq _

/-- A start law has no inaccessible states: every state can be reached from its
positive support (Theorem 1, condition (1), p. 43). -/
def Chain.AllAccessible (C : Chain X) (S : X → ℝ) : Prop :=
  ∀ x, ∃ (s : X) (n : ℕ), 0 < S s ∧ 0 < (C.P ^ n) s x

/-- Table 1, p. 35: expected reward on leaving `x`. -/
def Chain.rbar (C : Chain X) (R : X → X → ℝ) (x : X) : ℝ :=
  ∑ y, C.P x y * R x y

/-- The expected discounted return (p. 34). The Markov property identifies
`(P^k rbar)(x)` with the expected reward at step `k` from `x`. The theorems
assert summability explicitly, including at `γ=1`. -/
noncomputable def Chain.value (C : Chain X) (R : X → X → ℝ) (γ : ℝ) (x : X) : ℝ :=
  ∑' k : ℕ, γ ^ k * (Matrix.mulVec (C.P ^ k) (C.rbar R)) x

/-- Figure 2, p. 42: advance with `P` from a non-absorbing state and draw
again from the start law when the current trial has ended. -/
noncomputable def Chain.restartKernel (C : Chain X) (S : X → ℝ) : Matrix X X ℝ :=
  fun x y => if C.P x x = 1 then S y else C.P x y

end LeastSquaresTD.Absorbing


