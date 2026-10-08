-- Prove2me | Definitions.Def_HordijkKallenbergLP_Correspondence_Model
-- name    : HordijkKallenbergLP_Correspondence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:47.352379+00:00
-- url     : https://prove2.me/theorems/15da224e-19cc-43d9-bfb8-eb22f8a2efdf
-- title:
--   Finite MDP policies and the primal–dual LP model
-- statement:
--   Let $E$ be a nonempty finite state set. In each state $i$, the finite set $A(i)$ of available actions is nonempty. An action $a\in A(i)$ gives reward $r_{ia}$ and transition probabilities $p_{iaj}$. A stationary randomized policy $\pi$ has nonnegative weights, supported on $A(i)$, that sum to one at each state. Its transition matrix and reward vector are
--
--   $$P(\pi)_{ij}=\sum_{a\in A(i)}\pi_{ia}p_{iaj},\qquad r(\pi)_i=\sum_{a\in A(i)}\pi_{ia}r_{ia}.$$
--
--   A pair $(\phi,u)$ is superharmonic when $\phi_i\ge\sum_jp_{iaj}\phi_j$ and $\phi_i+u_i\ge r_{ia}+\sum_jp_{iaj}u_j$ for every admissible $(i,a)$. The primal minimizes $\sum_i\beta_i\phi_i$ over these pairs. The dual maximizes $\sum_{i,a}r_{ia}x_{ia}$ subject to the paper's flow equations (3)–(4) and $x,y\ge0$. Its action coordinates exist only for $a\in A(i)$. Write $E_x=\{i:\sum_a x_{ia}>0\}$ and normalize either $x$ or $y$ at each state to obtain the proposed policy $\pi(x,y)$.
--
--   These definitions fix the objects used throughout the correspondence theorem. **Formalization Note** Average optimality means equality with the supremum of liminf average rewards over all history-dependent randomized policies. The policy weights of an infeasible dual point can be undefined mathematically; their Lean quotient is used only after feasible-point well definedness has been established. The superharmonic predicate, the admissible-pair index type and the average-optimality predicate are taken from the shared definition `HordijkKallenbergLP.SingleLP.Model` (the same objects as in mission 1); this file adds the randomized policies, the primal and dual optimality predicates in the form used here, $E_x$ and $\pi(x,y)$.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, pp. 353, 356–357, 359, §§2.1, 3.2–3.3

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model

namespace HordijkKallenbergLP.Correspondence

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- Hordijk and Kallenberg (1979), §2.1, p. 353: a stationary randomized policy.
Formalization Note: weights outside the admissible action set are zero. -/
structure RandomizedPolicy (M : StationaryMDP S A) where
  weight : S → A → ℝ
  nonneg : ∀ i a, 0 ≤ weight i a
  supported : ∀ i a, a ∉ M.admissible i → weight i a = 0
  sum_one : ∀ i, ∑ a ∈ M.admissible i, weight i a = 1

/-- The history-independent policy induced by stationary randomized weights.
Hordijk and Kallenberg (1979), §2.1, p. 353. -/
def RandomizedPolicy.toHR {M : StationaryMDP S A} (π : RandomizedPolicy M) : AvgHRPolicy M where
  q := fun _ _ i a => π.weight i a
  nonneg := fun _ _ i a => π.nonneg i a
  sum_one := fun _ _ i => π.sum_one i

/-- The transition matrix `P(π)` of §3.3, p. 359. -/
def policyMatrix (M : StationaryMDP S A) (π : RandomizedPolicy M) : Matrix S S ℝ :=
  fun i j => ∑ a ∈ M.admissible i, π.weight i a * M.trans i a j

/-- The one-step reward vector `r(π)` of §3.3, p. 359. -/
def policyReward (M : StationaryMDP S A) (π : RandomizedPolicy M) : S → ℝ :=
  fun i => ∑ a ∈ M.admissible i, π.weight i a * M.reward i a

/-- The primal objective and feasible set of §3.2, p. 356. -/
def primalObjective (β φ : S → ℝ) : ℝ := ∑ i, β i * φ i

def PrimalFeasible (M : StationaryMDP S A) (φ u : S → ℝ) : Prop :=
  HordijkKallenbergLP.SingleLP.Superharmonic M φ u

def PrimalOptimal (M : StationaryMDP S A) (β φ u : S → ℝ) : Prop :=
  PrimalFeasible M φ u ∧
  ∀ φ' u', PrimalFeasible M φ' u' → primalObjective β φ ≤ primalObjective β φ'

noncomputable instance (M : StationaryMDP S A) : Fintype (HordijkKallenbergLP.SingleLP.Pair M) := by
  classical
  dsimp [HordijkKallenbergLP.SingleLP.Pair]
  infer_instance

/-- Total dual mass assigned to actions at a state. -/
noncomputable def stateMass (M : StationaryMDP S A) (x : HordijkKallenbergLP.SingleLP.Pair M → ℝ) (i : S) : ℝ :=
  ∑ p : HordijkKallenbergLP.SingleLP.Pair M, if p.1.1 = i then x p else 0

/-- The dual objective of §3.2, p. 357. -/
noncomputable def dualObjective (M : StationaryMDP S A) (x : HordijkKallenbergLP.SingleLP.Pair M → ℝ) : ℝ :=
  ∑ p, M.reward p.1.1 p.1.2 * x p

/-- Equations (3)–(5) of Hordijk and Kallenberg (1979), p. 357.
Formalization Note: the Kronecker-delta sum is written as an inflow balance. -/
def DualFeasible (M : StationaryMDP S A) (β : S → ℝ)
    (x y : HordijkKallenbergLP.SingleLP.Pair M → ℝ) : Prop :=
  (∀ p, 0 ≤ x p ∧ 0 ≤ y p) ∧
  (∀ j, stateMass M x j = ∑ p : HordijkKallenbergLP.SingleLP.Pair M, M.trans p.1.1 p.1.2 j * x p) ∧
  (∀ j, stateMass M x j + stateMass M y j =
      β j + ∑ p : HordijkKallenbergLP.SingleLP.Pair M, M.trans p.1.1 p.1.2 j * y p)

/-- Attainment of the dual maximum over the exact feasible set, p. 357. -/
def DualOptimal (M : StationaryMDP S A) (β : S → ℝ)
    (x y : HordijkKallenbergLP.SingleLP.Pair M → ℝ) : Prop :=
  DualFeasible M β x y ∧
  ∀ x' y', DualFeasible M β x' y' → dualObjective M x' ≤ dualObjective M x

/-- `E_x` of §2.2, p. 354, and §3.2, p. 357. -/
def Ex (M : StationaryMDP S A) (x : HordijkKallenbergLP.SingleLP.Pair M → ℝ) : Set S :=
  {i | 0 < stateMass M x i}

/-- The numerators in the two cases of the policy π(x,y), §3.3, p. 359. -/
noncomputable def dualPolicyWeight (M : StationaryMDP S A) (x y : HordijkKallenbergLP.SingleLP.Pair M → ℝ)
    (i : S) (a : A) : ℝ := by
  classical
  exact if h : a ∈ M.admissible i then
    if i ∈ Ex M x then
      x ⟨(i, a), h⟩ / stateMass M x i
    else
      y ⟨(i, a), h⟩ / stateMass M y i
  else 0

end HordijkKallenbergLP.Correspondence


