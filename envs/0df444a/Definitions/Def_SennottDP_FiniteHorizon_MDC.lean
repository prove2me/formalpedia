-- Prove2me | Definitions.Def_SennottDP_FiniteHorizon_MDC
-- name    : SennottDP_FiniteHorizon_MDC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T06:12:48.748086+00:00
-- url     : https://prove2.me/theorems/8a2543fb-ec80-4821-b5f0-f0ae82c81c80
-- title:
--   Markov decision chain, general policies and histories (Sennott §2.1–2.3)
-- statement:
--   A **Markov decision chain** (MDC) $\Delta$ consists of a countable state space $S$ and, for each state $i \in S$,
--
--   1. a finite nonempty set $A_i$ of actions;
--   2. a nonnegative finite cost $C(i,a) \ge 0$ incurred when action $a \in A_i$ is chosen in state $i$;
--   3. for each $a \in A_i$ a transition probability distribution $(P_{ij}(a))_{j \in S}$ with $\sum_{j} P_{ij}(a) = 1$.
--
--   A **history** at time $t$ is $h_t = (i_0, a_0, i_1, a_1, \dots, i_{t-1}, a_{t-1}, i_t)$. A **(general) policy** $\theta$ assigns to every history a probability distribution $\theta(\cdot \mid h_t)$ on the action set $A_{i_t}$ of the current state; it may depend on the entire history and may randomize. A **stationary policy** $f$ picks a fixed action $f(i) \in A_i$ in each state. A **deterministic Markov policy** $(g_0, g_1, \dots)$ uses the stationary policy $g_t$ at time $t$.
--
--   Under $\theta$ and initial state $X_0 = i$, the probability that the history at time $t$ equals $h_t$ is
--   $$
--   P_\theta(h_t \mid X_0 = i) = \prod_{s=0}^{t-1} \theta(a_s \mid h_s)\, P_{i_s i_{s+1}}(a_s), \qquad i_0 = i .
--   $$
--   The **continuation policy** $\psi(i,a,\cdot)$ of $\theta$ after initial state $i$ and initial action $a$ is the rule $\theta$ follows from time $1$ on, re-indexed so that time $1$ becomes time $0$: its history $(j, a_1, \dots)$ is $\theta$'s history $(i, a, j, a_1, \dots)$.
--
--   A stationary $f$ is a **limit point** of a sequence $(f_r)$ of stationary policies (Definition B.1) if some subsequence $(f_{r_k})$ satisfies, for each $i \in S$, $f_{r_k}(i) = f(i)$ for all sufficiently large $k$.
--
--   These are the objects about which every statement of the finite horizon theory is made.
--
--   **Formalization Note** A history is stored as the list of past state–action pairs, most recent first, together with the current state; `σ h i a` is $\theta(a \mid h)$, a probability distribution on $A_i$ (weights in $[0,\infty]$ summing to $1$ over $A_i$, zero off $A_i$). Policies are defined for all times; a policy for the $n$ horizon is the restriction of such a policy to times $0,\dots,n-1$, and only those decisions enter the $n$ horizon cost. `histProb θ i t h j` is $P_\theta$ of the history $(h, j)$ at time $t$; it is $0$ unless $h$ has length $t$. Countability of $S$ is a hypothesis of each theorem.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 15–16, Section 2.1 (MDC); pp. 20–22, Section 2.2 (policies); pp. 22–23, Section 2.3 (joint law); p. 38 (continuation policy ψ(i,a,j), proof of Theorem 3.1.2); pp. 288–289, Definition B.1

import Mathlib

open scoped ENNReal NNReal
open Classical

namespace SennottDP.FiniteHorizon

/-- A Markov decision chain `Δ` (Sennott, §2.1, pp. 15–16): for each state `i` a finite nonempty
action set `A i`, a nonnegative finite cost `C i a`, and for each `a ∈ A i` a transition
probability distribution `P i a ·` on the state space (`∑_j P_ij(a) = 1`). The state space is
countable wherever it is used (`[Countable S]` on the theorems). -/
structure MDC (S : Type) (Act : Type) where
  A : S → Finset Act
  A_nonempty : ∀ i, (A i).Nonempty
  C : S → Act → ℝ≥0
  P : S → Act → S → ℝ≥0∞
  P_sum : ∀ i, ∀ a ∈ A i, ∑' j, P i a j = 1

namespace MDC

variable {S Act : Type} (M : MDC S Act)

/-- A general (history-dependent, randomized) policy `θ` (§2.2, pp. 20–22). A history at time `t`
is `h_t = (i_0, a_0, …, i_{t-1}, a_{t-1}, i_t)`; it is encoded as the list of the past
state–action pairs, **most recent first**, `[(i_{t-1}, a_{t-1}), …, (i_0, a_0)]`, together with
the current state `i_t`. `σ h i a` is the probability `θ(a | h_t)` of choosing action `a`; it is a
probability distribution on `A i`. A policy for the `n` horizon (p. 22) is the restriction of such
a policy to the decisions at `t = 0, …, n − 1`. -/
structure Policy where
  σ : List (S × Act) → S → Act → ℝ≥0∞
  σ_sum : ∀ h i, ∑ a ∈ M.A i, σ h i a = 1
  σ_supp : ∀ h i a, a ∉ M.A i → σ h i a = 0

/-- A stationary policy `f` (p. 20): a distinguished action `f i ∈ A i` for every state `i`. -/
def Stationary : Type := {f : S → Act // ∀ i, f i ∈ M.A i}

variable {M}

/-- The deterministic Markov policy `(g 0, g 1, g 2, …)` (p. 21): at time `t`, in state `i`, it
chooses the action `(g t) i` with probability one. The time `t` is the length of the history. -/
noncomputable def Policy.ofMarkov (g : ℕ → M.Stationary) : M.Policy where
  σ h i a := if a = (g h.length).1 i then 1 else 0
  σ_sum h i := by simp [(g h.length).2 i]
  σ_supp h i a ha := by
    have : a ≠ (g h.length).1 i := fun e => ha (e ▸ (g h.length).2 i)
    simp [this]

/-- The continuation policy `ψ(i, a, ·)` of `θ` after the initial state `i` and the initial action
`a` (proof of Theorem 3.1.2, p. 38): it is the rule `θ` uses from time `t = 1` on, re-indexed so
that `t = 1` becomes time `0`. A history `(j, a_1, …, i_s)` of the continuation is the history
`(i, a, j, a_1, …, i_s)` of `θ`; with most-recent-first lists this appends `(i, a)` at the end. -/
noncomputable def Policy.shift (θ : M.Policy) (i : S) (a : Act) : M.Policy where
  σ h k b := θ.σ (h ++ [(i, a)]) k b
  σ_sum _ k := θ.σ_sum _ k
  σ_supp _ k b hb := θ.σ_supp _ k b hb

/-- `histProb θ i t h j` is the probability, under `θ` and initial state `X_0 = i`, that the history
at time `t` is `(h, j)` — past pairs `h` (most recent first, of length `t`) and current state
`X_t = j` (§2.3, pp. 22–23):
`P_θ(h_t) = ∏_{s<t} θ(a_s | h_s) P_{i_s i_{s+1}}(a_s)`. -/
noncomputable def histProb (θ : M.Policy) (i : S) : ℕ → List (S × Act) → S → ℝ≥0∞
  | 0, [], j => if j = i then 1 else 0
  | 0, _ :: _, _ => 0
  | _ + 1, [], _ => 0
  | t + 1, (k, a) :: h, j => histProb θ i t h k * θ.σ h k a * M.P k a j

/-- `f` is a limit point of the sequence `(f_r)` of stationary policies for `Δ` (Definition B.1,
pp. 288–289): there is a subsequence `f_{r_k}` such that for each state `i`,
`f_{r_k}(i) = f(i)` for all sufficiently large `k`. -/
def IsLimitPoint (fs : ℕ → M.Stationary) (f : M.Stationary) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∀ᶠ k in Filter.atTop, (fs (φ k)).1 i = f.1 i

end MDC

end SennottDP.FiniteHorizon


