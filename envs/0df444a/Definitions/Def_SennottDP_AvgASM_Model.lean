-- Prove2me | Definitions.Def_SennottDP_AvgASM_Model
-- name    : SennottDP_AvgASM_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T09:05:27.3749+00:00
-- url     : https://prove2.me/theorems/430ab68b-0752-411a-b2b2-cf986b7c193d
-- title:
--   Markov decision chain, general policies and the induced process (Sennott §2.1–2.3)
-- statement:
--   A **Markov decision chain** (MDC) $\Delta$ consists of a countable state space $S$; for each state $i$ a finite nonempty set $A_i$ of actions; a finite nonnegative cost $C(i,a)$ incurred when action $a$ is taken in state $i$; and for each $a\in A_i$ a probability distribution $(P_{ij}(a))_{j\in S}$ of the next state, so that
--   $$\sum_{j\in S} P_{ij}(a)=1 .$$
--
--   A **general policy** $\theta$ chooses, at each time $n$, the action randomly according to a distribution $\theta(\cdot\mid h_n)$ on $A_{i_n}$ that may depend on the whole history $h_n=(i_0,a_0,\dots,i_{n-1},a_{n-1},i_n)$. A **stationary policy** $f$ chooses the deterministic action $f(i)\in A_i$ whenever the state is $i$; it induces a Markov chain with transition probabilities $P_{ij}(f)=P_{ij}(f(i))$ and costs $C(i,f(i))$.
--
--   Given a policy $\theta$ and the initial state $X_0=i$, the probability of an initial segment of the state–action process is the product of the policy's choice probabilities and the transition probabilities, and the expected cost at time $t$ is
--   $$E_\theta[C(X_t,A_t)\mid X_0=i]=\sum_{h_t}P_\theta(h_t,a_t)\,C(i_t,a_t)\in[0,\infty].$$
--
--   These objects are the common model on which every optimization criterion of the book is built.
--
--   **Formalization Note** Histories are lists of state–action pairs, most recent first. A general policy is a function of the past list and the current state, supported on $A_i$ and summing to one there; stationary policies embed as point masses. The transition row $P_{i\cdot}(a)$ is required to be a distribution only for $a\in A_i$, as in the book. Expected costs are in $[0,\infty]$ (`ℝ≥0∞`).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 15–23, Sections 2.1–2.3

import Mathlib

namespace SennottDP.AvgASM

open scoped ENNReal NNReal

/-- A Markov decision chain `Δ` (Sennott, §2.1, pp. 15–16): a countable state space `S`, for each
state `i` a finite nonempty set of actions `A i`, nonnegative finite costs `C i a`, and for each
`a ∈ A i` a transition probability distribution `P i a ·` on `S` (`∑_j P_ij(a) = 1`). -/
structure MDC (S : Type*) (Act : Type*) [Countable S] where
  /-- the finite action set available in state `i` -/
  A : S → Finset Act
  /-- every action set is nonempty -/
  A_nonempty : ∀ i, (A i).Nonempty
  /-- the (finite, nonnegative) one-step cost -/
  C : S → Act → ℝ≥0
  /-- the transition probability from `i` to `j` under action `a` -/
  P : S → Act → S → ℝ≥0∞
  /-- for `a ∈ A i` the row `P i a ·` is a probability distribution on `S` -/
  P_sum : ∀ i, ∀ a ∈ A i, ∑' j, P i a j = 1

variable {S : Type*} {Act : Type*} [Countable S]

/-- A general (history-dependent, randomized) policy for the infinite horizon (§2.2, pp. 20–21).
At time `n` with history `h_n = (i_0, a_0, …, i_{n-1}, a_{n-1}, i_n)` the action is drawn from the
distribution `θ(· | h_n)` on `A_{i_n}`. The history is encoded by the list of past state-action
pairs, **most recent first**, together with the current state:
`prob [(i_{n-1},a_{n-1}), …, (i_0,a_0)] i_n a = θ(a | h_n)`. -/
structure Policy (M : MDC S Act) where
  /-- `prob past i a` is the probability of choosing `a` in current state `i` after `past` -/
  prob : List (S × Act) → S → Act → ℝ≥0∞
  /-- only actions of `A i` are chosen -/
  prob_supp : ∀ past i a, a ∉ M.A i → prob past i a = 0
  /-- the choice is a probability distribution on `A i` -/
  prob_sum : ∀ past i, ∑ a ∈ M.A i, prob past i a = 1

/-- A (deterministic) stationary policy `f` (§2.2, p. 20): an action `f i ∈ A i` for every
state. -/
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

/-- The transition matrix of the Markov chain induced by the stationary policy `e`
(p. 171, Appendix C): `P_ij(e) = P_ij(e(i))`. -/
def StationaryPolicy.chain {M : MDC S Act} (e : StationaryPolicy M) : S → S → ℝ≥0∞ :=
  fun i j => M.P i (e.f i) j

/-- The cost function of the Markov chain induced by the stationary policy `e`:
`C(i) = C(i, e(i))`. -/
def StationaryPolicy.cost {M : MDC S Act} (e : StationaryPolicy M) : S → ℝ≥0∞ :=
  fun i => (M.C i (e.f i) : ℝ≥0∞)

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

/-- The expected cost at time `t`, `E_θ[C(X_t, A_t) | X_0 = i]` (2.6), p. 23: the sum of
`C(i_t, a_t)` against the law of the length-`(t+1)` state-action history. Valued in `[0, ∞]`. -/
noncomputable def expCost {M : MDC S Act} (θ : Policy M) (i : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' h : List (S × Act), if h.length = t + 1 then histProb θ i h * lastCost M h else 0

end SennottDP.AvgASM


