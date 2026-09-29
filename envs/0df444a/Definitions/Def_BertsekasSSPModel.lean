-- Prove2me | Definitions.Def_BertsekasSSPModel
-- name    : BertsekasSSPModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-08T00:41:57.860391+00:00
-- url     : https://prove2.me/theorems/c8762bcc-bcc8-49d9-9765-de381bf1d372
-- title:
--   The stochastic shortest path model, its DP operators, and discounted variants
-- statement:
--   This module fixes the finite-state infinite-horizon framework of Bertsekas, Vol. I, Chapter 7: the stochastic shortest path model, its dynamic programming operators, the $N$-stage costs, the probabilities appearing in Assumptions 7.2.1 and 7.4.1, and the discounted variants of §7.3.
--
--   **The model.** States $1, \dots, n$ together with an implicit cost-free absorbing **termination state** $t$. At state $i$ a control $u$ from a finite nonempty set $U(i)$ is applied, incurring cost $g(i,u)$ and moving to state $j$ with probability $p_{ij}(u)$, where
--
--   $$p_{ij}(u) \ge 0, \qquad \sum_{j=1}^{n} p_{ij}(u) \;\le\; 1 ,$$
--
--   the deficit $1 - \sum_j p_{ij}(u)$ being the probability of terminating at that step.
--
--   **Operators.** For a stationary policy $\mu$ and a cost vector $J$,
--
--   $$(T_\mu J)(i) = g\bigl(i,\mu(i)\bigr) + \sum_{j} p_{ij}\bigl(\mu(i)\bigr) J(j), \qquad (TJ)(i) = \min_{u \in U(i)} \Bigl[ g(i,u) + \sum_j p_{ij}(u) J(j) \Bigr],$$
--
--   and their $\alpha$-discounted counterparts, in which the sum is multiplied by $\alpha$.
--
--   **$N$-stage costs.** For a possibly nonstationary policy $\pi = (\mu_0, \mu_1, \dots)$, the cost over $N$ stages with zero terminal cost is $J^N_\pi = T_{\mu_0} J^{N-1}_{\sigma\pi}$ with $J^0_\pi = 0$, where $\sigma\pi$ is $\pi$ shifted by one stage; the infinite-horizon cost is its limit.
--
--   **Probabilities in the assumptions.** The **survival** probability $P\{x_m \ne t\}$ after $m$ stages, and the probability of **avoiding** a designated state $s$ at all of the times $1, \dots, m$, are defined by the analogous recursions; Assumption 7.2.1 requires the first to be $< 1$ uniformly, and Assumption 7.4.1 the second.
--
--   This is the base case of the whole theory of Markov decision processes: the stochastic shortest path form is the most general of the three settings in the chapter, with the discounted case obtained by terminating with probability $1-\alpha$ per stage, and the average-cost case by cycling through a recurrent state.
--
--   **Formalization Note** The termination state is not a member of the carrier: termination is the sub-stochastic deficit, exactly as the source treats it computationally. Row sums are constrained only at admissible controls. Constraint sets are finite and nonempty, so the minimum in $T$ is attained. Policies are sequences of stage policies, and the costs of nonstationary policies are defined via the shift recursion; the discounted model reuses the same carrier, with stochastic rows imposed as a hypothesis where needed.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 7.2; D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 7.1; D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 7.2, Eq. (7.6)/(7.7); D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 7.2, Assumption 7.2.1; D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 7.4, Assumption 7.4.1; D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 7.3

import Mathlib

/-- The finite-state stochastic shortest path model of Bertsekas, "Dynamic
Programming and Optimal Control", Vol. I, 3rd ed., Section 7.2: states
`1, …, n` (here `Fin n`) plus an implicit cost-free absorbing termination
state `t`.  Applying control `u ∈ U i` at state `i` incurs cost `g i u`,
moves to state `j` with probability `p i u j`, and moves to the termination
state with the remaining probability `1 - ∑ⱼ p i u j`. -/
structure BertsekasSSPModel (n : ℕ) (C : Type) [Fintype C] where
  U : Fin n → Finset C
  hU : ∀ i, (U i).Nonempty
  p : Fin n → C → Fin n → ℝ
  g : Fin n → C → ℝ
  hp_nonneg : ∀ i u j, 0 ≤ p i u j
  hp_sum : ∀ i, ∀ u ∈ U i, ∑ j, p i u j ≤ 1

/-- An admissible (nonstationary, state-feedback) policy for the stochastic
shortest path model: a sequence of stage policies, each respecting the control
constraint sets. -/
def BertsekasSSPAdmissible {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (π : ℕ → Fin n → C) : Prop :=
  ∀ k i, π k i ∈ M.U i

/-- The DP operator `T_μ` associated with a stationary policy `μ` for the
stochastic shortest path model:
`(T_μ J)(i) = g(i, μ(i)) + ∑ⱼ p_{ij}(μ(i)) J(j)`. -/
def BertsekasSSPPolicyOp {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (μ : Fin n → C) (J : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => M.g i (μ i) + ∑ j, M.p i (μ i) j * J j

/-- The Bellman (value iteration) operator `T` of the stochastic shortest path
model: `(T J)(i) = min_{u ∈ U(i)} [g(i, u) + ∑ⱼ p_{ij}(u) J(j)]`
(Eq. (7.6)/(7.7)). -/
noncomputable def BertsekasSSPBellmanOp {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (J : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (M.U i).inf' (M.hU i) fun u => M.g i u + ∑ j, M.p i u j * J j

/-- The `N`-stage expected cost of a (possibly nonstationary) policy `π` for
the stochastic shortest path model, with zero terminal cost:
`BertsekasSSPNCost M π N i = E[∑_{k<N} g(x_k, μ_k(x_k)) | x₀ = i]`.
The infinite-horizon cost of `π` is the limit as `N → ∞`. -/
def BertsekasSSPNCost {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) : (ℕ → Fin n → C) → ℕ → Fin n → ℝ
  | _, 0 => 0
  | π, N + 1 =>
      BertsekasSSPPolicyOp M (π 0)
        (BertsekasSSPNCost M (fun k => π (k + 1)) N)

/-- `BertsekasSSPSurvival M π m i` is the probability that the termination
state has not been reached after `m` stages, starting from state `i` and using
policy `π` — the quantity `P{x_m ≠ t | x₀ = i, π}` of Assumption 7.2.1. -/
def BertsekasSSPSurvival {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) : (ℕ → Fin n → C) → ℕ → Fin n → ℝ
  | _, 0 => fun _ => 1
  | π, m + 1 => fun i =>
      ∑ j, M.p i (π 0 i) j *
        BertsekasSSPSurvival M (fun k => π (k + 1)) m j

open Classical in
/-- `BertsekasSSPAvoidProb M s π m i` is the probability that the designated
state `s` is not visited during the first `m` stages (i.e. by any of
`x₁, …, x_m`), starting from `x₀ = i` under policy `π`.  Assumption 7.4.1 of
Section 7.4 requires this to be `< 1` for some `m`, uniformly over policies
and initial states. -/
noncomputable def BertsekasSSPAvoidProb {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (s : Fin n) :
    (ℕ → Fin n → C) → ℕ → Fin n → ℝ
  | _, 0 => fun _ => 1
  | π, m + 1 => fun i =>
      ∑ j, if j = s then 0 else
        M.p i (π 0 i) j *
          BertsekasSSPAvoidProb M s (fun k => π (k + 1)) m j

/-- The DP operator `T_μ` of the α-discounted finite-state problem of
Section 7.3: `(T_μ J)(i) = g(i, μ(i)) + α ∑ⱼ p_{ij}(μ(i)) J(j)`. -/
def BertsekasDiscountedPolicyOp {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (α : ℝ) (μ : Fin n → C) (J : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => M.g i (μ i) + α * ∑ j, M.p i (μ i) j * J j

/-- The Bellman operator of the α-discounted finite-state problem of
Section 7.3 (Eq. (7.21)/(7.22)):
`(T J)(i) = min_{u ∈ U(i)} [g(i, u) + α ∑ⱼ p_{ij}(u) J(j)]`. -/
noncomputable def BertsekasDiscountedBellmanOp {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (α : ℝ) (J : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (M.U i).inf' (M.hU i) fun u =>
    M.g i u + α * ∑ j, M.p i u j * J j

/-- The `N`-stage expected α-discounted cost of a (possibly nonstationary)
policy `π`: `BertsekasDiscountedNCost M α π N i =
E[∑_{k<N} α^k g(x_k, μ_k(x_k)) | x₀ = i]`. -/
def BertsekasDiscountedNCost {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (α : ℝ) : (ℕ → Fin n → C) → ℕ → Fin n → ℝ
  | _, 0 => 0
  | π, N + 1 =>
      BertsekasDiscountedPolicyOp M α (π 0)
        (BertsekasDiscountedNCost M α (fun k => π (k + 1)) N)


