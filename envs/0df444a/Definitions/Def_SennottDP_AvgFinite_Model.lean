-- Prove2me | Definitions.Def_SennottDP_AvgFinite_Model
-- name    : SennottDP_AvgFinite_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T08:03:20.404453+00:00
-- url     : https://prove2.me/theorems/9b21e235-4be1-46fe-8847-24c1398eb923
-- title:
--   Markov decision chain, general policies, stationary policies and the expected cost at time t
-- statement:
--   A **Markov decision chain** (MDC) $\Delta$ consists of
--
--   1. a countable state space $S$;
--   2. for each state $i$, a finite nonempty set $A_i$ of actions;
--   3. a nonnegative finite cost $C(i,a)$ incurred when action $a$ is chosen in state $i$;
--   4. transition probabilities $P_{ij}(a) \ge 0$ with $\sum_{j \in S} P_{ij}(a) = 1$: if $a$ is chosen in $i$, the next state is $j$ with probability $P_{ij}(a)$.
--
--   A **policy** $\theta$ (general, history dependent and randomized) chooses the action at time $t$ from a probability distribution $\theta(\cdot \mid h_t)$ on $A_{i_t}$ that may depend on the whole history
--   $$h_t = (i_0, a_0, i_1, a_1, \ldots, i_{t-1}, a_{t-1}, i_t).$$
--   A **stationary policy** $f$ assigns to each state $i$ a fixed action $f(i) \in A_i$ and always chooses it; it is the special general policy with $\theta(f(i_t) \mid h_t) = 1$.
--
--   Given the initial state $X_0 = i$, a policy determines the joint law of the states $X_t$ and actions $A_t$: the probability of the history $(i_0,a_0,\ldots,i_t,a_t)$ is
--   $$\mathbf 1\{i_0 = i\}\,\theta(a_0 \mid h_0)\,\prod_{s=1}^{t} P_{i_{s-1} i_s}(a_{s-1})\,\theta(a_s \mid h_s).$$
--   The **statistical average cost at time $t$** is
--   $$E_\theta[C(X_t,A_t) \mid X_0 = i] = \sum_{j} \sum_{a \in A_j} C(j,a)\, P_\theta(X_t = j, A_t = a \mid X_0 = i) \in [0,\infty].$$
--
--   These objects are the common substrate of every criterion (discounted and average cost) in the mission.
--
--   **Formalization Note** States and actions are types `S` (with `[Countable S]`) and `Act`; `A i : Finset Act`. Costs are in `ℝ≥0`, transition probabilities in `ℝ≥0∞` and are given for every action (only those in `A i` are ever used). A policy is a function `prob past i a` of the list of past state-action pairs (**most recent first**) and the current state, supported on `A i` and summing to one there. `expCost θ i t` sums `C(i_t,a_t)` against the law of the length-$(t+1)$ history, in `ℝ≥0∞`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 16, Section 2.1; pp. 20–21, Section 2.2; pp. 22–23, Section 2.3, Eq. (2.6)

import Mathlib

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal

/-- A Markov decision chain (Sennott, §2.1, p. 16): a countable state space `S`, for each state
`i` a finite nonempty set of actions `A i`, nonnegative finite costs `C i a`, and transition
probabilities `P i a j` with `∑' j, P i a j = 1`. -/
structure MDC (S : Type*) (Act : Type*) [Countable S] where
  /-- the finite action set available in state `i` -/
  A : S → Finset Act
  /-- every action set is nonempty -/
  A_nonempty : ∀ i, (A i).Nonempty
  /-- the (finite, nonnegative) one-step cost -/
  C : S → Act → ℝ≥0
  /-- the transition probability from `i` to `j` under action `a` -/
  P : S → Act → S → ℝ≥0∞
  /-- each row is a probability distribution on `S` -/
  P_sum : ∀ i a, ∑' j, P i a j = 1

variable {S : Type*} {Act : Type*} [Countable S]

/-- A general (history-dependent, randomized) policy for the infinite horizon (§2.2, p. 20).
At time `n` with history `h_n = (i_0, a_0, …, i_{n-1}, a_{n-1}, i_n)` the action is drawn from the
distribution `θ(· | h_n)` on `A_{i_n}`. The history is encoded by the list of past state-action
pairs, **most recent first**, together with the current state: `prob [(i_{n-1},a_{n-1}), …,
(i_0,a_0)] i_n a = θ(a | h_n)`. -/
structure Policy (M : MDC S Act) where
  /-- `prob past i a` is the probability of choosing `a` in current state `i` after `past` -/
  prob : List (S × Act) → S → Act → ℝ≥0∞
  /-- only actions of `A i` are chosen -/
  prob_supp : ∀ past i a, a ∉ M.A i → prob past i a = 0
  /-- the choice is a probability distribution on `A i` -/
  prob_sum : ∀ past i, ∑ a ∈ M.A i, prob past i a = 1

/-- A (deterministic) stationary policy `f` (§2.2, p. 20): a distinguished action `f i ∈ A i` for
every state. -/
structure StationaryPolicy (M : MDC S Act) where
  /-- the action chosen in state `i` -/
  f : S → Act
  /-- the action is admissible -/
  mem : ∀ i, f i ∈ M.A i

open Classical in
/-- A stationary policy regarded as a general policy: it chooses `f i` with probability one. -/
noncomputable def StationaryPolicy.toPolicy {M : MDC S Act} (e : StationaryPolicy M) :
    Policy M where
  prob := fun _ i a => if a = e.f i then 1 else 0
  prob_supp := by
    intro past i a ha
    have : a ≠ e.f i := fun h => ha (h ▸ e.mem i)
    simp [this]
  prob_sum := by
    intro past i
    simp [e.mem i]

open Classical in
/-- Weight of the transition into the state `j` that follows the (most-recent-first) list `rest`:
the initial indicator `1{j = i}` if `rest` is empty, and `P_{k j}(b)` if the last pair of `rest`
is `(k, b)`. -/
noncomputable def prevWeight (M : MDC S Act) (i : S) : List (S × Act) → S → ℝ≥0∞
  | [], j => if j = i then 1 else 0
  | (k, b) :: _, j => M.P k b j

/-- `histProb θ i h` is `P_θ(X_0 = i_0, A_0 = a_0, …, X_t = i_t, A_t = a_t | X_0 = i)` for the list
`h = [(i_t,a_t), …, (i_0,a_0)]` (most recent first) (§2.3, pp. 22–23). -/
noncomputable def histProb {M : MDC S Act} (θ : Policy M) (i : S) : List (S × Act) → ℝ≥0∞
  | [] => 1
  | (j, a) :: rest => histProb θ i rest * prevWeight M i rest j * θ.prob rest j a

/-- The cost of the most recent state-action pair of a history (`0` for the empty list). -/
noncomputable def lastCost (M : MDC S Act) : List (S × Act) → ℝ≥0∞
  | [] => 0
  | (j, a) :: _ => (M.C j a : ℝ≥0∞)

/-- The statistical average cost at time `t`, `E_θ[C(X_t, A_t) | X_0 = i]` (2.6), p. 23: the sum
of `C(i_t, a_t)` against the law of the length-`(t+1)` state-action history. Valued in `[0, ∞]`. -/
noncomputable def expCost {M : MDC S Act} (θ : Policy M) (i : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' h : List (S × Act), if h.length = t + 1 then histProb θ i h * lastCost M h else 0

end SennottDP.AvgFinite


