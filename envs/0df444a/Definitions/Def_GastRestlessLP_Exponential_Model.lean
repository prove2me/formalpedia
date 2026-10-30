-- Prove2me | Definitions.Def_GastRestlessLP_Exponential_Model
-- name    : GastRestlessLP_Exponential_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:16:14.984563+00:00
-- url     : https://prove2.me/theorems/4c9ed03a-40b9-48ee-b286-0602766faa07
-- title:
--   Identical restless arms, occupation vectors, and mean transition
-- statement:
--   An arm is a finite Markov decision process with two actions, passive $0$ and active $1$. Its transition probabilities $P^a_{s,r}$ are nonnegative and each row sums to one. Rewards $R_s^a$ are arbitrary real numbers. The model stores the initial target vector $m_0$ as the underlying MDP's initial law $\rho$, and a binding activation fraction $0<\alpha<1$. The finite state set is nonempty in the theorem statements.
--
--   An occupation vector $y$ records the fractions in each state and action. Its state marginal is $m_s=\sum_a y_{s,a}$; its one-step reward is $\sum_{s,a}R_s^a y_{s,a}$. The real simplex consists of nonnegative vectors summing to one, including boundary points. The norm is explicitly $\|m\|_1=\sum_s|m_s|$.
--
--   The mean transition is $\phi(y)_s=\sum_{r,a}y_{r,a}P^a_{r,s}$. This uses the intended departure-state subscript in (7), as dictated by (4b) and the conditional expectation on p. 5. The printed subscript typo is recorded as I1. The generic MDP is referenced, not redeclared.
-- source:
--   Gast, Gaujal and Yan, arXiv:2106.10067v3 (22 December 2023), https://arxiv.org/abs/2106.10067v3, pp. 4–7, (1), (4), (7)

import Mathlib
import Definitions.Def_DouyinDQ_Bias_FiniteMDP

open scoped BigOperators

namespace GastRestlessLP.Exponential

/-- Probability vectors, including the boundary of the real simplex. -/
def InSimplex {S : Type} [Fintype S] (m : S → ℝ) : Prop :=
  (∀ s, 0 ≤ m s) ∧ ∑ s, m s = 1

/-- Identical two-action arms, their initial empirical target, and the binding fraction.
The generic MDP stores arbitrary real rewards and the initial target in `ρ`. -/
structure Model (S : Type) [Fintype S] where
  arm : DouyinDQ.Bias.MDP S (Fin 2)
  stochastic : arm.Standing
  α : ℝ
  α_pos : 0 < α
  α_lt_one : α < 1

variable {S : Type} [Fintype S]

/-- State-action occupation vectors use action 0 for passive and 1 for active. -/
abbrev Allocation (S : Type) := S → Fin 2 → ℝ

/-- L1 norm, not the sup norm on a function type. -/
def l1 (m : S → ℝ) : ℝ := ∑ s, |m s|

/-- State marginal of an occupation vector. -/
def marginal (y : Allocation S) (s : S) : ℝ := ∑ a, y s a

/-- Mean transition (4b): the allocation is indexed by the departure state.
This is the intended reading of the summation-index typo in (7). -/
def phi (M : Model S) (y : Allocation S) (s : S) : ℝ :=
  ∑ r, ∑ a, y r a * M.arm.P a r s

/-- One epoch's reward per arm. -/
def reward (M : Model S) (y : Allocation S) : ℝ :=
  ∑ s, ∑ a, M.arm.r s a * y s a

end GastRestlessLP.Exponential


