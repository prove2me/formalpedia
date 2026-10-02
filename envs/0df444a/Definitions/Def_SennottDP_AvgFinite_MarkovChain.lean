-- Prove2me | Definitions.Def_SennottDP_AvgFinite_MarkovChain
-- name    : SennottDP_AvgFinite_MarkovChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T08:08:07.153835+00:00
-- url     : https://prove2.me/theorems/6cb3f8ac-22ca-4483-945a-ab10da96bc02
-- title:
--   Finite Markov chains: first passage times, positive recurrence, communicating classes, steady state probabilities
-- statement:
--   Let $(P_{ij})_{i,j \in S}$ be the transition matrix of a Markov chain on a finite state space $S$.
--
--   1. $P^{(t)}_{ij}$ is the $t$-step transition probability, with $P^{(0)}_{ij} = \delta_{ij}$. State $i$ **leads to** $j$ if $P^{(t)}_{ij} > 0$ for some $t \ge 0$; the **communicating class** of $z$ is the set of $j$ such that $z$ leads to $j$ and $j$ leads to $z$.
--   2. For $G \subseteq S$ the **first passage time** $T_{iG} = \min\{t \ge 1 : X_t \in G\}$ (with $X_0 = i$) always makes at least one transition. We write $P(T_{iG} = t)$ for its law and $P(T_{iG} < \infty) = \sum_t P(T_{iG} = t)$.
--   3. The **expected first passage time** is $m_{ij} = E[T_{ij}]$, with $m_{ij} = \infty$ when $P(T_{ij} < \infty) < 1$. State $i$ is **positive recurrent** if the return time satisfies $P(T_{ii} < \infty) = 1$ and $m_{ii} < \infty$.
--   4. The **steady state probability** of $j$ is $\pi_j = (m_{jj})^{-1}$, interpreted as $0$ if $m_{jj} = \infty$.
--   5. For a state $z$ and $g \ge 0$ on $S$, write
--   $$E\Big[\sum_{s=0}^{T_{iz}-1} g(X_s)\,;\ T_{iz} < \infty\Big]$$
--   for the expected $g$-cost accumulated before first reaching $z$, on the event that $z$ is reached; with $g \equiv 1$ this is $E[T_{iz};\ T_{iz} < \infty]$. It is computed from the **taboo probabilities** $P(X_s = j,\ T_{iz} > s)$.
--   6. A set $Z$ of **distinguished states** contains exactly one state $z_k$ from each positive recurrent class $R_k$.
--
--   These notions describe the chain induced by a stationary policy, whose positive recurrent classes and first passage quantities enter the average cost optimality equation.
--
--   **Formalization Note** The transition matrix is `Q : S → S → ℝ≥0∞` with `[Fintype S]`. The law of $T_{iG}$ is computed by the first-step recursion $P(T_{iG} = 1) = \sum_{k \in G} P_{ik}$, $P(T_{iG} = t+1) = \sum_{k \notin G} P_{ik} P(T_{kG} = t)$. The book defines $\pi_j$ as the Cesàro limit of $P^{(t)}_{jj}$ and notes that $\pi_j = (m_{jj})^{-1}$; the formalization takes the latter as the definition. `onHitSum Q z g i` is $\sum_{s \ge 0} \sum_j P(X_s = j, T_{iz} > s)\, g(j)\, P(T_{jz} < \infty)$, which is the expectation in item 5 by the Markov property.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 292–295, Section C.1; p. 298, Section C.2; p. 302, Section C.3; p. 101, Section 6.3

import Mathlib

namespace SennottDP.AvgFinite

open scoped ENNReal

/-! Markov chains on a finite state space (Sennott, Appendix C.1–C.3, pp. 292–302).
A chain is given by its transition matrix `Q : S → S → ℝ≥0∞`; the results that use these
definitions always supply a stochastic `Q` (a row of an MDC under a stationary policy). -/

variable {S : Type*} [Fintype S]

open Classical in
/-- The `t`-step transition probabilities `P^{(t)}_{ij}`, with `P^{(0)}_{ij} = δ_{ij}`
(p. 292). -/
noncomputable def nStep (Q : S → S → ℝ≥0∞) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | n + 1, i, j => ∑ k, nStep Q n i k * Q k j

/-- `i` leads to `j`: `P^{(t)}_{ij} > 0` for some `t ≥ 0` (p. 293). -/
def LeadsTo (Q : S → S → ℝ≥0∞) (i j : S) : Prop :=
  ∃ t : ℕ, nStep Q t i j ≠ 0

/-- The communicating class of `z`: the states `j` such that `z` leads to `j` and `j` leads to `z`
(p. 293). -/
def commClass (Q : S → S → ℝ≥0∞) (z : S) : Set S :=
  {j | LeadsTo Q z j ∧ LeadsTo Q j z}

open Classical in
/-- `firstPassage Q G t i = P(T_{iG} = t | X_0 = i)`, where the first passage time
`T_{iG} = min {t ≥ 1 : X_t ∈ G}` always makes at least one transition (p. 295). -/
noncomputable def firstPassage (Q : S → S → ℝ≥0∞) (G : Set S) : ℕ → S → ℝ≥0∞
  | 0, _ => 0
  | t + 1, i =>
      if t = 0 then ∑ k, (if k ∈ G then Q i k else 0)
      else ∑ k, (if k ∈ G then 0 else Q i k * firstPassage Q G t k)

/-- `P(T_{iG} < ∞)`: the probability that the chain started at `i` ever reaches `G`
(in at least one transition). -/
noncomputable def reachProb (Q : S → S → ℝ≥0∞) (G : Set S) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, firstPassage Q G t i

open Classical in
/-- The expected first passage time `m_{ij} = E[T_{ij}]` from `i` to `j`, which is `∞` when
`P(T_{ij} < ∞) < 1` (pp. 293, 295). -/
noncomputable def meanPassage (Q : S → S → ℝ≥0∞) (j i : S) : ℝ≥0∞ :=
  if reachProb Q {j} i = 1 then ∑' t : ℕ, (t : ℝ≥0∞) * firstPassage Q {j} t i else ⊤

/-- State `i` is positive recurrent: the return time `T` to `i` satisfies `P(T < ∞) = 1` and
`m_{ii} = E[T] < ∞` (p. 293). -/
def PositiveRecurrent (Q : S → S → ℝ≥0∞) (i : S) : Prop :=
  reachProb Q {i} i = 1 ∧ meanPassage Q i i ≠ ⊤

/-- The steady state probability `π_j = (m_{jj})^{-1}`, interpreted as `0` when `m_{jj} = ∞`
(p. 294). -/
noncomputable def steadyState (Q : S → S → ℝ≥0∞) (j : S) : ℝ≥0∞ :=
  (meanPassage Q j j)⁻¹

open Classical in
/-- Taboo probabilities for the taboo state `z`: `tabooStep Q z s i j` is the probability of being
in `j` at time `s` without having visited `z` at any of the times `1, …, s`
(`tabooStep Q z 0 i j = δ_{ij}`). Equivalently `P(X_s = j, T_{iz} > s | X_0 = i)`. -/
noncomputable def tabooStep (Q : S → S → ℝ≥0∞) (z : S) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | s + 1, i, j => if j = z then 0 else ∑ k, tabooStep Q z s i k * Q k j

/-- `onHitSum Q z g i = E[∑_{s=0}^{T-1} g(X_s) ; T < ∞ | X_0 = i]` with `T = T_{iz}` the first
passage time to `z`: the expected `g`-cost accumulated before reaching `z`, counted on the event
that `z` is reached. With `g ≡ 1` it is `E[T ; T < ∞]`. -/
noncomputable def onHitSum (Q : S → S → ℝ≥0∞) (z : S) (g : S → ℝ≥0∞) (i : S) : ℝ≥0∞ :=
  ∑' s : ℕ, ∑ j, tabooStep Q z s i j * g j * reachProb Q {z} j

/-- `Z` is a set of distinguished states, one from each positive recurrent class
(Sennott p. 101: "for `1 ≤ k ≤ K` select a distinguished state `z_k ∈ R_k`"): every element of `Z`
is positive recurrent, distinct elements lie in distinct classes, and every positive recurrent
state communicates with some element of `Z`. -/
def IsDistinguishedSet (Q : S → S → ℝ≥0∞) (Z : Finset S) : Prop :=
  (∀ z ∈ Z, PositiveRecurrent Q z) ∧
  (∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → z' ∉ commClass Q z) ∧
  (∀ j, PositiveRecurrent Q j → ∃ z ∈ Z, j ∈ commClass Q z)

end SennottDP.AvgFinite


