-- Prove2me | Definitions.Def_MatrixAnalytic_Tree_Process
-- name    : MatrixAnalytic_Tree_Process
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:46.778844+00:00
-- url     : https://prove2.me/theorems/c6547360-0553-4d78-93b2-035ac06e4381
-- title:
--   Continuous-time Markov processes on a countable state space — generator, jump chain, expected times, recurrence, positive recurrence, stationary vector
-- statement:
--   Chapter 14 studies a continuous-time Markov process on a countable state space $S$, given by an **infinitesimal generator** $Q = (Q_{xy})_{x,y \in S}$. This file fixes the probabilistic vocabulary for such a process.
--
--   1. $Q$ is a **generator** if $Q_{xy} \ge 0$ for $x \ne y$ and every row sums to zero, $\sum_y Q_{xy} = 0$ (so every total exit rate is finite). It is **irreducible** if every state leads to every other one through a finite chain of transitions with strictly positive rates.
--   2. The **holding rate** of $x$ is $q_x = -Q_{xx}$; each visit to $x$ lasts an exponential time with mean $1/q_x$. The **embedded jump chain** has transition matrix $P_{xy} = Q_{xy}/q_x$ for $y \ne x$ and $P_{xx} = 0$ (an absorbing state with $q_x = 0$ keeps $P_{xx} = 1$).
--   3. The weight of a finite trajectory $\omega_0, \dots, \omega_t$ of the jump chain is $P_{\omega_0\omega_1}\cdots P_{\omega_{t-1}\omega_t}$. The expected number of visits to $y$, starting from $x$, before the first visit to a set $T$ after time $0$, is $\sum_{t \ge 0}$ of the total weight of the trajectories from $x$ that are in $y$ at time $t$ and avoid $T$ at times $1, \dots, t$ (the visit at time $0$ counts). For $y$ in a set $S'$, the **first-entry probability** from $x$ to $y$ is the total weight of the trajectories from $x$ that avoid $S'$ at times $1, \dots, t$ and are in $y$ at time $t+1$, summed over $t \ge 0$.
--   4. The **expected time** spent in $y$, starting from $x$, before the first visit to $T$, is the expected number of visits of the jump chain to $y$ before $T$ multiplied by the mean holding time $1/q_y$.
--   5. A state $x$ is **recurrent** if the probability that the jump chain started at $x$ has not returned to $x$ by its $t$-th jump tends to $0$ as $t \to \infty$. Its **expected return time** $m_x$ is the sum over all states $y$ of the expected time spent in $y$, starting from $x$, before the first return to $x$ (the initial sojourn in $x$ included). The state is **positive recurrent** if it is recurrent and $m_x < \infty$. The process is recurrent (positive recurrent) if every state is.
--   6. A **stationary probability vector** is a row vector $\pi$ with $\pi \ge 0$, $\pi\mathbf 1 = 1$ and $\pi Q = 0$.
--
--   For an irreducible positive recurrent process the stationary probability vector exists and is unique; it is the vector the book calls the stationary distribution.
--
--   **Formalization Note** The process is encoded by its jump chain and holding rates, which describes the minimal process; recurrence implies that it does not explode. All probabilities and expected times are sums of nonnegative trajectory weights computed in $[0, \infty]$ (`ℝ≥0∞`), so an infinite expected time is represented as $\infty$, never by a junk value. The only junk value is $1/q_x = 0$ at an absorbing state, which an irreducible generator on two or more states does not have; for a one-state process it makes the state positive recurrent, which agrees with the usual convention that an absorbing state is positive recurrent (Norris, *Markov Chains*, 1997, §3.5). The discrete-time bodies follow the platform definition `mm_countable` (namespace `MarkovMixing`), which is not importable in this environment.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 288–290 (Chapter 14, a continuous-time Markov process with generator (14.2)); bodies follow the platform definition mm_countable

import Mathlib

namespace MatrixAnalytic.Tree

noncomputable section

open scoped ENNReal

/-!
Continuous-time Markov processes on a countable state space, given by an infinitesimal generator
`Q` (the setting of Chapter 14 of Latouche & Ramaswami, where the state space is the countable set
of stacks of a tree process). The process is encoded by its **embedded jump chain**
`P_{xy} = Q_{xy} / q_x` (`x ≠ y`) and its **holding rates** `q_x = −Q_{xx}`: the time spent in a
state per visit is exponential with mean `1 / q_x`. Every probability is a sum, over finite
trajectories of the jump chain, of products of one-step jump probabilities, and every expected time
is an expected number of visits of the jump chain multiplied by the mean holding time. All these
quantities take values in `ℝ≥0∞`. None of them is defined through an equation of the chapter.
-/

variable {V : Type*} [Countable V] [DecidableEq V]

/-- `Q` is a (conservative) **infinitesimal generator**: off-diagonal rates are nonnegative and
every row sums to `0` (in particular the total rate out of every state is finite). -/
def IsGenerator (Q : V → V → ℝ) : Prop :=
  (∀ x y : V, x ≠ y → 0 ≤ Q x y) ∧ ∀ x : V, HasSum (Q x) 0

/-- The generator is **irreducible**: every state leads to every other state through a chain of
transitions with strictly positive rates. -/
def IsIrreducibleGen (Q : V → V → ℝ) : Prop :=
  ∀ x y : V, Relation.ReflTransGen (fun u v : V => u ≠ v ∧ 0 < Q u v) x y

/-- The holding rate `q_x = −Q_{xx}`: the sojourn time in `x` is exponential with mean `1 / q_x`. -/
def holdRate (Q : V → V → ℝ) (x : V) : ℝ := -Q x x

/-- The transition matrix of the embedded jump chain: `P_{xy} = Q_{xy} / q_x` for `y ≠ x` and
`P_{xx} = 0` when `q_x > 0`; an absorbing state (`q_x = 0`) stays where it is. -/
def jumpP (Q : V → V → ℝ) (x y : V) : ℝ :=
  if holdRate Q x = 0 then (if y = x then 1 else 0)
  else (if y = x then 0 else Q x y / holdRate Q x)

/-- The weight `P_{ω₀ω₁} ⋯ P_{ω_{t−1}ω_t}` of a trajectory of length `t` of a chain with transition
matrix `P`, in `ℝ≥0∞`: the probability, starting from `ω₀`, that `X₁ = ω₁, …, X_t = ω_t`. -/
def pathWeightE (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
/-- The expected number of visits of the chain `P` to the state `y`, starting from `X₀ = x`,
before its first visit to the set `T` after time `0`:
`Σ_{t ≥ 0} P[X_t = y, X₁ ∉ T, …, X_t ∉ T | X₀ = x]`. The visit at time `0` counts when `y = x`. -/
def expVisitsAvoid (P : V → V → ℝ) (T : Set V) (x y : V) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ s : Fin (t + 1), s ≠ 0 → ω s ∉ T
    then pathWeightE P ω else 0

open Classical in
/-- For `y ∈ S`: the probability that the chain `P`, started at `X₀ = x`, visits the set `S` at
some time `≥ 1` and that its first such visit is to the state `y`:
`Σ_{t ≥ 0} P[X₁ ∉ S, …, X_t ∉ S, X_{t+1} = y | X₀ = x]`. -/
def firstEntryProb (P : V → V → ℝ) (S : Set V) (x y : V) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 2) → V,
    if ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧
        ∀ s : Fin (t + 2), s ≠ 0 → s ≠ Fin.last (t + 1) → ω s ∉ S
    then pathWeightE P ω else 0

/-- The expected total **time** the process with generator `Q` spends in the state `y`, starting
from `x` at time `0`, before its first visit to the set `T` (after leaving `x`): the expected
number of visits of the jump chain to `y` before `T`, times the mean holding time `1 / q_y`. -/
def sojournAvoid (Q : V → V → ℝ) (T : Set V) (x y : V) : ℝ≥0∞ :=
  expVisitsAvoid (jumpP Q) T x y * ENNReal.ofReal (holdRate Q y)⁻¹

open Classical in
/-- `P_x[τ⁺_x > t]` for the jump chain: the probability that the jump chain started at `x` has
not returned to `x` at any of the jumps `1, …, t`. -/
def returnTail (Q : V → V → ℝ) (x : V) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ∀ s : Fin (t + 1), s ≠ 0 → ω s ≠ x then pathWeightE (jumpP Q) ω else 0

/-- The state `x` is **recurrent**: the process started in `x` returns to `x` with probability one
(the return-time tails of the jump chain tend to `0`). -/
def RecurrentState (Q : V → V → ℝ) (x : V) : Prop :=
  Filter.Tendsto (fun t => returnTail Q x t) Filter.atTop (nhds 0)

/-- The expected first return time `m_x` of the process to `x`, starting from `x`: the sum, over
the states `y`, of the expected time spent in `y` before the first return to `x` (the initial
sojourn in `x` included). -/
def expReturnTime (Q : V → V → ℝ) (x : V) : ℝ≥0∞ :=
  ∑' y : V, sojournAvoid Q {x} x y

/-- The state `x` is **positive recurrent**: it is recurrent and its expected return time is
finite. -/
def PositiveRecurrentState (Q : V → V → ℝ) (x : V) : Prop :=
  RecurrentState Q x ∧ expReturnTime Q x < ⊤

/-- The process is **recurrent**: every state is recurrent. -/
def IsRecurrentProcess (Q : V → V → ℝ) : Prop :=
  ∀ x : V, RecurrentState Q x

/-- The process is **positive recurrent**: every state is positive recurrent. -/
def IsPositiveRecurrentProcess (Q : V → V → ℝ) : Prop :=
  ∀ x : V, PositiveRecurrentState Q x

/-- A **stationary probability vector** of the process: `π ≥ 0`, `π1 = 1` and `πQ = 0`. -/
def IsStationaryCT (Q : V → V → ℝ) (π : V → ℝ) : Prop :=
  (∀ x : V, 0 ≤ π x) ∧ HasSum π 1 ∧ ∀ y : V, HasSum (fun x => π x * Q x y) 0

end

end MatrixAnalytic.Tree


