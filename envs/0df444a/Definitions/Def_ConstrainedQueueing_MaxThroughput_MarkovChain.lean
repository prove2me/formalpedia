-- Prove2me | Definitions.Def_ConstrainedQueueing_MaxThroughput_MarkovChain
-- name    : ConstrainedQueueing_MaxThroughput_MarkovChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:19.55324+00:00
-- url     : https://prove2.me/theorems/35fe212f-b40b-49b8-867f-a65e76b7df24
-- title:
--   Definition 3.1, p. 1938 — countable Markov chains: reachability, transient set T, first entry, positive recurrence, stability
-- statement:
--   Let $\sigma$ be a state space and $P=(P_{xy})_{x,y\in\sigma}$ a transition matrix with entries in $[0,\infty]$; $P$ is **stochastic** when every row sums to one, $\sum_y P_{xy}=1$. The $n$-step probabilities are $P^{(0)}_{xy}=\mathbf 1[x=y]$ and $P^{(n+1)}_{xy}=\sum_z P_{xz}P^{(n)}_{zy}$.
--
--   1. A state $y$ is **reachable** from $x$ if $P^{(n)}_{xy}>0$ for some $n\ge 1$.
--   2. A state $x$ is **essential** if every state reachable from $x$ reaches $x$ back. For a stochastic matrix the essential states are exactly the states lying in some closed set of communicating states $R_1,R_2,\dots$; the **transient set** $T$ is the set of states that are not essential.
--   3. For a set of states $B$, the **first-entry probability** $F_B^{(n)}(x)$ is the probability that the chain started at $X(0)=x$ enters $B$ for the first time at time $n\ge 1$:
--   $$F_B^{(1)}(x)=\sum_{y\in B}P_{xy},\qquad F_B^{(n+1)}(x)=\sum_{y\notin B}P_{xy}\,F_B^{(n)}(y),$$
--   and $F_B^{(0)}=0$. The **hitting probability** is $h_B(x)=\sum_{n\ge1}F_B^{(n)}(x)$. With $B=T^{c}$, $h_B(x)=P(\tau_x<\infty)$ for the time $\tau_x=\min\{t>0: X(t)\notin T\}$ of (3.1).
--   4. The first-passage probabilities to a state are $f^{(n)}_{xy}=F^{(n)}_{\{y\}}(x)$; the return probability is $f_{xx}=\sum_{n}f^{(n)}_{xx}$ and the mean recurrence time is $m_{xx}=\sum_n n f^{(n)}_{xx}\in[0,\infty]$. A state is **positive recurrent** if $f_{xx}=1$ and $m_{xx}<\infty$.
--
--   **Definition 3.1.** The chain is **stable** if
--   $$P(\tau_y<\infty)=1\quad\forall y\in T\qquad\text{(3.1a)}$$
--   and all states $x\in\bigcup_{j}R_j$ are positive recurrent.
--
--   This notion of stability allows reducible chains: the queue-length chain of a constrained network need not be irreducible, and stability asks that it leaves the transient states almost surely and is positive recurrent on every closed class.
--
--   **Formalization Note.** Definition 3.1 is stated through the transition matrix (first-entry series), not through a path measure; all probabilities are $[0,\infty]$-valued. $\bigcup_j R_j$ is encoded as the set of essential states. The names follow the published Gross et al. Markov-chain definitions, restated on a general state type.
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1938, §III, (3.1), (3.1a), Definition 3.1

import Mathlib

open scoped ENNReal

namespace ConstrainedQueueing.MaxThroughput

/-! Countable-state Markov chains given by a transition matrix `P : σ → σ → ℝ≥0∞`
(Tassiulas–Ephremides 1992, §III, p. 1938). The names and conventions follow the published
`QueueingFundamentals.Foundations.MarkovChain` (Gross et al.), restated on a general state type
and with `ℝ≥0∞` values throughout, since the queue-length chain lives on `ℕ^{queues}`. -/

variable {σ : Type*}

/-- `P` is a stochastic matrix: every row sums to one. -/
def IsStochastic (P : σ → σ → ℝ≥0∞) : Prop :=
  ∀ x, ∑' y, P x y = 1

open Classical in
/-- The `n`-step transition probabilities `P(X(t + n) = y | X(t) = x)`: the identity at `n = 0`,
and `P^{(n+1)}_{xy} = ∑_z P_{xz} P^{(n)}_{zy}`. -/
noncomputable def stepProb (P : σ → σ → ℝ≥0∞) : ℕ → σ → σ → ℝ≥0∞
  | 0, x, y => if x = y then 1 else 0
  | n + 1, x, y => ∑' z, P x z * stepProb P n z y

/-- `y` is reachable from `x` (p. 1938: "a state `x` is reachable by some state `y` if
`P(X(t + n) = x | X(t) = y) > 0` for some `n ≥ 1`"), here with the roles named
`Reaches P x y` = "`y` is reachable by `x`". The page's `n ≥ 1` is kept. -/
def Reaches (P : σ → σ → ℝ≥0∞) (x y : σ) : Prop :=
  ∃ n, 1 ≤ n ∧ 0 < stepProb P n x y

/-- `x` is essential: every state reachable from `x` reaches `x` back. For a stochastic `P` these are
exactly the states lying in some closed set of communicating states `R_j` of p. 1938: the set
`{y | Reaches P x y}` of an essential `x` is closed and its states communicate (and it contains `x`,
since a row summing to one gives some successor `y`, which reaches `x` back); conversely every state
of a closed communicating set is essential, because whatever it reaches stays in the set. -/
def IsEssential (P : σ → σ → ℝ≥0∞) (x : σ) : Prop :=
  ∀ y, Reaches P x y → Reaches P y x

/-- The set `T` of p. 1938: the states that belong to no closed set of communicating states. -/
def transientSet (P : σ → σ → ℝ≥0∞) : Set σ :=
  {x | ¬ IsEssential P x}

/-- `firstEntry P B n x` is the probability, for the chain started at `X(0) = x`, that the first time
`t > 0` with `X(t) ∈ B` equals `n`. It is `0` at `n = 0`; at `n = 1` it is `P(x, B)`; and a first
entry at time `n + 2` makes a first step to some `y ∉ B` followed by a first entry at time `n + 1`. -/
noncomputable def firstEntry (P : σ → σ → ℝ≥0∞) (B : Set σ) : ℕ → σ → ℝ≥0∞
  | 0, _ => 0
  | 1, x => ∑' y, B.indicator (P x) y
  | n + 2, x => ∑' y, Bᶜ.indicator (fun y => P x y * firstEntry P B (n + 1) y) y

/-- The probability that the chain started at `x` enters `B` at some time `t > 0`. With
`B = Tᶜ` this is `P(τ_x < ∞)` for the time `τ_x` of (3.1). -/
noncomputable def hitProb (P : σ → σ → ℝ≥0∞) (B : Set σ) (x : σ) : ℝ≥0∞ :=
  ∑' n, firstEntry P B n x

/-- First-passage probabilities `f_{xy}^{(n)}`: the first visit to `y` at a time `t > 0` happens at
`t = n` (for `y = x`, the first return). -/
noncomputable def firstPassage (P : σ → σ → ℝ≥0∞) (n : ℕ) (x y : σ) : ℝ≥0∞ :=
  firstEntry P {y} n x

/-- `f_{xx} = ∑_{n ≥ 1} f_{xx}^{(n)}`, the probability of ever returning to `x`. -/
noncomputable def returnProb (P : σ → σ → ℝ≥0∞) (x : σ) : ℝ≥0∞ :=
  ∑' n, firstPassage P n x x

/-- The mean recurrence time `m_{xx} = ∑_{n ≥ 1} n f_{xx}^{(n)}`, in `[0, ∞]`. -/
noncomputable def meanRecurrenceTime (P : σ → σ → ℝ≥0∞) (x : σ) : ℝ≥0∞ :=
  ∑' n : ℕ, (n : ℝ≥0∞) * firstPassage P n x x

/-- `x` is positive recurrent: it is recurrent (`f_{xx} = 1`) with finite mean recurrence time. -/
def PositiveRecurrentState (P : σ → σ → ℝ≥0∞) (x : σ) : Prop :=
  returnProb P x = 1 ∧ meanRecurrenceTime P x < ⊤

/-- **Definition 3.1** (p. 1938). The chain is stable if `P(τ_y < ∞) = 1` for every `y ∈ T` (3.1a)
and every state of `⋃_j R_j` (the essential states) is positive recurrent. Stated through the
transition matrix: `P(τ_y < ∞)` is `hitProb P Tᶜ y`. -/
def IsStable (P : σ → σ → ℝ≥0∞) : Prop :=
  (∀ y ∈ transientSet P, hitProb P (transientSet P)ᶜ y = 1) ∧
    ∀ x, IsEssential P x → PositiveRecurrentState P x

end ConstrainedQueueing.MaxThroughput


