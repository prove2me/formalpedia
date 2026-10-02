-- Prove2me | Definitions.Def_SennottDP_MarkovCost_Chain
-- name    : SennottDP_MarkovCost_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T13:39:08.898273+00:00
-- url     : https://prove2.me/theorems/248ae794-accb-4207-bb7f-ea8dbdbc0e3d
-- title:
--   Markov chains on a countable state space: first passages, taboo probabilities, classes and steady state probabilities
-- statement:
--   A **Markov chain** $\Gamma$ on a countable state space $S$ is given by transition probabilities $P_{ij} \ge 0$, $i,j \in S$, with $\sum_j P_{ij} = 1$ for every $i$. Write $X_t$ for the state at time $t$. The $t$-step transition probabilities $P^{(t)}_{ij}$ are the entries of the matrix power $\mathbf P^t$, with $P^{(0)}_{ij} = \delta_{ij}$. The probability that the chain started at $x_0$ follows the path $x_0, x_1, \dots, x_t$ is $\prod_{s<t} P_{x_s x_{s+1}}$.
--
--   Fix a nonempty set $G \subseteq S$ and a state $i$.
--
--   1. The **first passage time** $T_{iG} = \min\{t \ge 1 : X_t \in G\}$ (so $T_{iG} \ge 1$, and $T_{iG} = \infty$ if $G$ is never entered), started from $X_0 = i$.
--   2. The **taboo probability** $_G P^{(t)}_{ik}$ is the probability of going from $i$ to $k$ in $t$ slots without visiting $G$ at the intermediate times $1, \dots, t-1$; the endpoints may lie in $G$. Thus $_G P^{(0)}_{ik} = \delta_{ik}$ and $_G P^{(1)}_{ik} = P_{ik}$.
--   3. $_G u_{ik}$ is the expected number of visits to $k$ in a first passage from $i$ to $G$, counting the times $0 \le t < T_{iG}$:
--   $$ {}_G u_{ik} = \sum_{t \ge 0} P(X_t = k,\ T_{iG} > t \mid X_0 = i) \in [0,\infty]. $$
--   4. $P(T_{iG} = t \mid X_0 = i) = \sum_{k \in G} {}_G P^{(t)}_{ik}$ for $t \ge 1$, and $P(T_{iG} < \infty \mid X_0=i) = \sum_{t \ge 1} P(T_{iG} = t \mid X_0=i)$.
--   5. The **expected first passage time** $m_{iG} = E[T_{iG}]$ equals $\sum_{t\ge1} t\,P(T_{iG}=t \mid X_0=i)$ if $P(T_{iG} < \infty)=1$, and $\infty$ otherwise. For $G = \{j\}$ it is written $m_{ij}$; $m_{ii}$ is the expected return time to $i$.
--
--   State $i$ **leads to** $j$ if $P^{(t)}_{ij} > 0$ for some $t \ge 0$; $i$ and $j$ **communicate** if each leads to the other, and the chain is **irreducible** if all states communicate. State $i$ is **transient** if $P(T_{ii} < \infty) < 1$ and **positive recurrent** if $P(T_{ii} < \infty) = 1$ and $m_{ii} < \infty$. A **positive recurrent class** is a communicating class all of whose states are positive recurrent. The **steady state probability** of $j$ is
--   $$ \pi_j = (m_{jj})^{-1}, $$
--   read as $0$ when $m_{jj} = \infty$.
--
--   These are the objects of Appendix C used throughout the book's average cost theory.
--
--   **Formalization Note** Probabilities and expectations are `ℝ≥0∞`-valued sums over finite paths `Fin (t+1) → S`, so no summability side conditions arise and $0\cdot\infty = 0$. The book introduces $\pi_j$ as the Cesàro limit $\lim_n Q^{(n)}_{jj}$ and states that it equals $(m_{jj})^{-1}$; the latter is taken as the definition. Positive recurrence of a class is required of every state of the class.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 292–295, Section C.1 (transition matrix, classes, recurrence, (C.1) and π_j = (m_jj)^{-1}, taboo probabilities, T_iG, _G u_ik, m_iG)

import Mathlib

open scoped ENNReal NNReal

namespace SennottDP.MarkovCost

/-- Sennott (1999), App. C.1, p. 292: a Markov chain `Γ` on a countable state space `S`, given by
its matrix of transition probabilities `P i j` (the probability that `Γ` moves to `j` during the
next slot when it is in `i`), with `∑_j P_{ij} = 1` for every `i`. -/
structure MC (S : Type) [Countable S] where
  /-- the transition probability `P_{ij}` -/
  P : S → S → ℝ≥0∞
  /-- every row sums to one -/
  P_sum : ∀ i, ∑' j, P i j = 1

variable {S : Type} [Countable S]

open Classical in
/-- Sennott (1999), p. 292: the `t`-step transition probability `P^{(t)}_{ij}`, the `ij`th entry of
the product matrix `P^t`, with `P^{(0)}_{ij} = δ_{ij}`. -/
noncomputable def nStep (M : MC S) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | t + 1, i, j => ∑' k, nStep M t i k * M.P k j

/-- The probability `∏_{s<t} P_{x_s x_{s+1}}` that the chain, started at `x_0`, follows the path
`x_0, x_1, …, x_t` during its first `t` transitions. -/
noncomputable def pathProb (M : MC S) {t : ℕ} (x : Fin (t + 1) → S) : ℝ≥0∞ :=
  ∏ s : Fin t, M.P (x s.castSucc) (x s.succ)

open Classical in
/-- Sennott (1999), p. 295: the taboo probability `_G P^{(t)}_{ik}` of going from `i` to `k` in `t`
slots while avoiding the taboo set `G` at the intermediate times `1, …, t − 1` (the initial state
`i` and the terminal state `k` may lie in `G`). It is the total probability of the paths
`x_0 = i, x_1, …, x_t = k` with `x_s ∉ G` for `0 < s < t`; hence `_G P^{(0)}_{ik} = δ_{ik}` and
`_G P^{(1)}_{ik} = P_{ik}`. -/
noncomputable def taboo (M : MC S) (G : Set S) (t : ℕ) (i k : S) : ℝ≥0∞ :=
  ∑' x : Fin (t + 1) → S,
    if x 0 = i ∧ x (Fin.last t) = k ∧ (∀ s : Fin (t + 1), 0 < s.val → s.val < t → x s ∉ G)
    then pathProb M x else 0

open Classical in
/-- `P(X_t = k, T_{iG} > t | X_0 = i)`: the chain started at `i` is in `k` at time `t` and has not
entered `G` at any of the times `1, …, t` (so the first passage time `T_{iG}` to `G` exceeds `t`).
For `t = 0` it is `δ_{ik}`. -/
noncomputable def avoidProb (M : MC S) (G : Set S) (t : ℕ) (i k : S) : ℝ≥0∞ :=
  ∑' x : Fin (t + 1) → S,
    if x 0 = i ∧ x (Fin.last t) = k ∧ (∀ s : Fin (t + 1), 0 < s.val → x s ∉ G)
    then pathProb M x else 0

/-- Sennott (1999), p. 295: `_G u_{ik}`, the expected number of visits to `k` in a first passage
from `i` to `G`, i.e. `E[#{t : 0 ≤ t < T_{iG}, X_t = k} | X_0 = i]`, where `T_{iG} ≥ 1` is the first
passage time from `i` to `G`. Visits at time `0` are counted and the visit at time `T_{iG}` is not,
which gives the book's conventions `_G u_{ik} = 0` for `k ∈ G`, `i ∉ G` and `_G u_{ik} = δ_{ik}`
for `k ∈ G`, `i ∈ G`. The value is in `[0, ∞]`. -/
noncomputable def visits (M : MC S) (G : Set S) (i k : S) : ℝ≥0∞ :=
  ∑' t : ℕ, avoidProb M G t i k

open Classical in
/-- `P(T_{iG} = t | X_0 = i)`: the law of the first passage time
`T_{iG} = min {t ≥ 1 : X_t ∈ G}` (p. 295). It is `0` for `t = 0` (since `T_{iG} ≥ 1`), and for
`t ≥ 1` it is `∑_{k ∈ G} _G P^{(t)}_{ik}`. -/
noncomputable def firstPassProb (M : MC S) (G : Set S) (i : S) (t : ℕ) : ℝ≥0∞ :=
  if t = 0 then 0 else ∑' k, if k ∈ G then taboo M G t i k else 0

/-- `P(T_{iG} < ∞ | X_0 = i)`, the probability that the chain started at `i` enters `G` at some
time `t ≥ 1`. -/
noncomputable def hitProb (M : MC S) (G : Set S) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, firstPassProb M G i t

open Classical in
/-- Sennott (1999), p. 295: the expected first passage time `m_{iG} = E[T_{iG}]`, computed from the
law of `T_{iG}` as a `[0, ∞]`-valued expectation: `∑_t t · P(T_{iG} = t)` when
`P(T_{iG} < ∞) = 1`, and `∞` when `P(T_{iG} < ∞) < 1` (then `T_{iG} = ∞` with positive
probability). For `G = {j}` this is `m_{ij}`; `m_{ii}` is the expected return time to `i`. -/
noncomputable def meanPassage (M : MC S) (G : Set S) (i : S) : ℝ≥0∞ :=
  if hitProb M G i = 1 then ∑' t : ℕ, (t : ℝ≥0∞) * firstPassProb M G i t else ⊤

/-- Sennott (1999), p. 293: `i` leads to `j` if `P^{(t)}_{ij} > 0` for some `t ≥ 0`. -/
def LeadsTo (M : MC S) (i j : S) : Prop :=
  ∃ t : ℕ, 0 < nStep M t i j

/-- Sennott (1999), p. 293: `i` and `j` communicate if each leads to the other. -/
def Communicate (M : MC S) (i j : S) : Prop :=
  LeadsTo M i j ∧ LeadsTo M j i

/-- The communicating class of `i`: the states that communicate with `i` (p. 293). -/
def commClass (M : MC S) (i : S) : Set S :=
  {j | Communicate M i j}

/-- Sennott (1999), p. 293: `Γ` is irreducible if `S` is a single communicating class. -/
def Irreducible (M : MC S) : Prop :=
  ∀ i j, Communicate M i j

/-- Sennott (1999), p. 293: `i` is transient if the return time `T` to `i` satisfies
`P(T < ∞) < 1`. -/
def Transient (M : MC S) (i : S) : Prop :=
  hitProb M {i} i < 1

/-- Sennott (1999), p. 293: `i` is positive recurrent if `P(T < ∞) = 1` for the return time `T`
to `i` and `m_{ii} = E[T] < ∞`. -/
def PositiveRecurrent (M : MC S) (i : S) : Prop :=
  hitProb M {i} i = 1 ∧ meanPassage M {i} i < ⊤

/-- Sennott (1999), p. 293: `R` is a positive recurrent class: `R` is a communicating class (the
class of one of its states) and every state of `R` is positive recurrent. -/
def IsPosRecClass (M : MC S) (R : Set S) : Prop :=
  (∃ i, R = commClass M i) ∧ ∀ j ∈ R, PositiveRecurrent M j

/-- Sennott (1999), p. 294: the steady state probability `π_j = (m_{jj})^{-1}`, interpreted as `0`
when `m_{jj} = ∞` (the book introduces `π_j` as `lim_n Q^{(n)}_{jj}` and states that it equals
`(m_{jj})^{-1}`). -/
noncomputable def steadyState (M : MC S) (j : S) : ℝ≥0∞ :=
  (meanPassage M {j} j)⁻¹

end SennottDP.MarkovCost


