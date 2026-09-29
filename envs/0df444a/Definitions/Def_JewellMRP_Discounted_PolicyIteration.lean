-- Prove2me | Definitions.Def_JewellMRP_Discounted_PolicyIteration
-- name    : JewellMRP_Discounted_PolicyIteration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:58:29.302774+00:00
-- url     : https://prove2.me/theorems/0dbcabc1-0089-40ab-ac9e-853a304580dc
-- title:
--   Policy returns, optimal $n$-step returns (6), value-determination equations (15) and the policy-improvement step of Fig. 1
-- statement:
--   This file defines the returns of policies and the two steps of the policy-iteration algorithm of Fig. 1 in Jewell (1963), for a Markov-renewal program with states $S$, alternatives $A$, and a fixed continuous discount factor $\alpha$.
--
--   1. A **stationary policy** is a map $d : S \to A$ choosing an alternative in each state. A **nonstationary policy** is a sequence $\pi = (\pi_0, \pi_1, \dots)$ of such maps, $\pi_k$ being used at the $k$-th transition.
--   2. The **$n$-step return** of $\pi$ with boundary rewards $V^0 = (V^0_i)_{i\in S}$ (the $V_i(0,\alpha)$ of p. 942) is defined by $V^\pi(0) = V^0$ and
--   $$
--   V^\pi_i(n+1) = \rho^{\pi_0(i)}_i(\alpha) + \sum_j p^{\pi_0(i)}_{ij}\,\tilde f^{\pi_0(i)}_{ij}(\alpha)\, V^{\pi'}_j(n),
--   $$
--   where $\pi' = (\pi_1, \pi_2, \dots)$ is the shifted policy. A stationary policy $d$ is the constant sequence $(d, d, \dots)$.
--   3. The **optimal $n$-step returns** $V_i(n,\alpha)$ of (6): $V_i(0,\alpha) = V^0_i$ and
--   $$
--   V_i(n,\alpha) = \max_z \Big[\rho^z_i(\alpha) + \sum_{j} p^z_{ij}\,\tilde f^z_{ij}(\alpha)\, V_j(n-1,\alpha)\Big], \qquad n = 1, 2, \dots
--   $$
--   4. A vector $v$ **solves the value-determination equations (15)** of a stationary policy $d$ if
--   $$
--   v_i = \rho^{d(i)}_i(\alpha) + \sum_{j} p^{d(i)}_{ij}\,\tilde f^{d(i)}_{ij}(\alpha)\, v_j \quad \text{for every } i .
--   $$
--   5. A policy $d'$ is obtained from $d$ and returns $v$ by the **policy-improvement step** of Fig. 1 if, in every state $i$, $d'(i)$ maximizes the test quantity $\rho^z_i(\alpha) + \sum_j p^z_{ij}\tilde f^z_{ij}(\alpha) v_j$ over $z$, and $d'(i) = d(i)$ whenever $d(i)$ already attains that maximum ("if there is no improvement in the test quantity from the last cycle, retain the same alternative").
--   6. A **run of the algorithm of Fig. 1** is a sequence of policies $d_0, d_1, \dots$ and returns $v_0, v_1, \dots$ such that $v_k$ solves (15) for $d_k$ and $d_{k+1}$ is obtained from $d_k$ and $v_k$ by the policy-improvement step, for every cycle $k$.
--
--   These objects state the convergence claims (a)–(d) of p. 946 and the optimality of the stationary policy the algorithm returns.
--
--   **Formalization Note** The paper defines $V_i(n,\alpha)$ as an expected discounted return of the Markov-renewal process; here the return of a policy is defined by the one-step recursion that the paper derives from the process (the policy form of (6)), the discount over the first interval averaging to $\tilde f^z_{ij}(\alpha)$ given $i$ and $j$. Policies are deterministic and Markov, as in the paper's description of the decision process (p. 942); nonstationary policies are indexed by the number of transitions already made. The equations (15) are kept as a predicate rather than defining the return of $d$ through a matrix inverse. The retention rule is read as: the old alternative is kept whenever it attains the maximum. Fig. 1's alternative start ("guess an initial set of returns") is covered by starting a run from the policy produced by the first improvement step.
-- source:
--   Jewell, Markov-Renewal Programming. I: Formulation, Finite Return Models, Operations Research 11(6), 1963, p. 942 (The Decision Process; Finite Step, Discounted Case, eq. (6)), p. 945 (eq. (15)), p. 947 (Fig. 1)

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP

namespace JewellMRP.Discounted

variable {S A : Type*} [Fintype S]

/-- The `n`-step discounted return of a (possibly nonstationary) policy `π`, with boundary
rewards `V0` (the `V_i(0, α)` of p. 942). `π k i` is the alternative used in state `i` at the
`k`-th transition (`k = 0, 1, 2, …`, counted from the start). A stationary policy `d : S → A`
is the constant sequence `fun _ => d`. -/
noncomputable def policyReturn (M : MRP S A) (α : ℝ) :
    (ℕ → S → A) → (S → ℝ) → ℕ → S → ℝ
  | _, V0, 0 => V0
  | π, V0, n + 1 => fun i =>
      test M α (π 0 i) i (policyReturn M α (fun k => π (k + 1)) V0 n)

/-- The optimal `n`-step discounted returns `V_i(n, α)` of the recurrence (6), with boundary
rewards `V_i(0, α) = V0 i`. -/
noncomputable def optValue [Fintype A] [Nonempty A] (M : MRP S A) (α : ℝ) (V0 : S → ℝ) :
    ℕ → S → ℝ
  | 0 => V0
  | n + 1 => maxTest M α (optValue M α V0 n)

/-- The value-determination equations (15) of the stationary policy `d`:
`v_i = ρ^{d(i)}_i(α) + Σ_j p^{d(i)}_{ij} f̃^{d(i)}_{ij}(α) v_j` for every state `i`. -/
def SolvesEval (M : MRP S A) (α : ℝ) (d : S → A) (v : S → ℝ) : Prop :=
  ∀ i, v i = test M α (d i) i v

/-- The policy-improvement step of Fig. 1: in every state `i`, the new alternative `d' i`
maximizes the test quantity computed with the present returns `v`; and if the old alternative
`d i` already attains that maximum (no improvement in the test quantity), it is retained. -/
def IsImprovement [Fintype A] [Nonempty A] (M : MRP S A) (α : ℝ) (d : S → A) (v : S → ℝ)
    (d' : S → A) : Prop :=
  ∀ i, test M α (d' i) i v = maxTest M α v i ∧
    (test M α (d i) i v = maxTest M α v i → d' i = d i)

/-- A run of the algorithm of Fig. 1: `d k` is the policy of cycle `k`, `v k` solves the
value-determination equations (15) for it, and `d (k + 1)` is obtained from `d k` and `v k` by
the policy-improvement step. -/
def IsFig1Run [Fintype A] [Nonempty A] (M : MRP S A) (α : ℝ) (d : ℕ → S → A)
    (v : ℕ → S → ℝ) : Prop :=
  ∀ k, SolvesEval M α (d k) (v k) ∧ IsImprovement M α (d k) (v k) (d (k + 1))

end JewellMRP.Discounted


