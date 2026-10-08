-- Prove2me | Definitions.Def_SSPAnalysis_Bellman_Model
-- name    : SSPAnalysis_Bellman_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:29:22.689985+00:00
-- url     : https://prove2.me/theorems/cf2888d5-33d7-40c7-aa3d-5a0ff11a5350
-- title:
--   Finite-state controlled Markov model and Bellman mappings
-- statement:
--   A finite-state controlled Markov model has states $1,\ldots,n$, a control set $U(i)$ at each state, a real one-stage cost $c_i(u)$, and transition probabilities $p_{ij}(u)$. Each probability row is nonnegative and sums to one. A selector $\mu$ chooses one control at each state; a policy $\pi$ is a sequence of selectors, and a stationary policy repeats one selector. The induced transition matrix and cost vector are $P(\mu)$ and $c(\mu)$. The Bellman mappings are
--
--   $$T_\mu(x)=c(\mu)+P(\mu)x,\qquad [T(x)]_i=\inf_{u\in U(i)}\left(c_i(u)+\sum_j p_{ij}(u)x_j\right).$$
--
--   This is the general finite-state stochastic-control substrate used by the paper's shortest-path assumptions and by all subsequent mission items.
--
--   **Formalization Note.** The paper's state $i$ is `i-1 : Fin n`. Probability-row conditions are made explicit. `TRealValued` records the paper's statement that $T$ maps real vectors to real vectors: each control family is nonempty and its one-stage Bellman values are bounded below. The separate shortest-path definition adds costs, properness, and Assumptions 1 and 2.
-- source:
--   Bertsekas and Tsitsiklis, An Analysis of Stochastic Shortest Path Problems, Math. Oper. Res. 16(3) (1991), pp. 582–583, §2, equations (5)–(6)

import Mathlib

namespace SSPAnalysis.Bellman

open Matrix Filter Topology

/-- A finite-state controlled Markov chain with a real one-stage cost and a
probability distribution on next states for every state and control. The paper's
state `i` is `i-1 : Fin n`. -/
structure Model (n : ℕ) (U : Fin n → Type*) where
  c : (i : Fin n) → U i → ℝ
  p : (i : Fin n) → U i → Fin n → ℝ
  p_nonneg : ∀ i u j, 0 ≤ p i u j
  p_sum_one : ∀ i u, ∑ j, p i u j = 1

/-- A stationary choice of one admissible control at each state. -/
abbrev Selector {n : ℕ} (U : Fin n → Type*) := (i : Fin n) → U i

/-- A possibly nonstationary sequence of state-control selectors. -/
abbrev Policy {n : ℕ} (U : Fin n → Type*) := ℕ → Selector U

/-- The policy which uses the same selector at every time. -/
def stationary {n : ℕ} {U : Fin n → Type*} (μ : Selector U) : Policy U :=
  fun _ => μ

namespace Model

variable {n : ℕ} {U : Fin n → Type*} (m : Model n U)

/-- The transition matrix induced by a selector. -/
def P (μ : Selector U) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => m.p i (μ i) j

/-- The vector of one-stage costs induced by a selector. -/
def cvec (μ : Selector U) : Fin n → ℝ :=
  fun i => m.c i (μ i)

/-- Equation (5), the Bellman operator for a fixed selector. -/
def Tmu (μ : Selector U) (x : Fin n → ℝ) : Fin n → ℝ :=
  m.cvec μ + m.P μ *ᵥ x

/-- Equation (6), the coordinatewise Bellman infimum. Its real value is
meaningful when each control family is nonempty and bounded below. -/
noncomputable def T (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ⨅ u : U i, (m.c i u + ∑ j, m.p i u j * x j)

/-- The real-valuedness implicit in the paper's notation `T : ℝⁿ → ℝⁿ`. -/
def TRealValued : Prop :=
  ∀ (x : Fin n → ℝ) (i : Fin n), Nonempty (U i) ∧
    BddBelow (Set.range fun u : U i => m.c i u + ∑ j, m.p i u j * x j)

end Model

end SSPAnalysis.Bellman


