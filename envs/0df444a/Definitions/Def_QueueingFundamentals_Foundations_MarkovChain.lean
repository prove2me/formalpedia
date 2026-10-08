-- Prove2me | Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
-- name    : QueueingFundamentals_Foundations_MarkovChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T06:34:49.413004+00:00
-- url     : https://prove2.me/theorems/4c123237-753e-40af-9d88-dd8771fc357c
-- title:
--   Discrete-parameter Markov chains on {0, 1, 2, …}: recurrence, periodicity, stationarity
-- statement:
--   A homogeneous discrete-parameter Markov chain on the state space $\{0,1,2,\dots\}$ is described by its transition matrix $P=\{p_{ij}\}$, where $p_{ij}=\Pr\{X_n=j\mid X_{n-1}=i\}$ does not depend on $n$. Every entry is nonnegative and every row sums to one.
--
--   This file introduces, for such a matrix:
--
--   1. the $m$-step transition probabilities $p_{ij}^{(m)}$, the entries of $P^{(m)}=P\cdot P^{(m-1)}$, $P^{(0)}=I$ (Eq. (1.21));
--   2. the first-passage probabilities $f_{ij}^{(n)}$: the probability that the chain started in $i$ enters $j$ for the first time at step $n\ge 1$ (for $i=j$, the first return at step $n$), with $f_{ij}^{(1)}=p_{ij}$ and $f_{ij}^{(n+1)}=\sum_{k\ne j}p_{ik}f_{kj}^{(n)}$;
--   3. the return probability $f_{jj}=\sum_{n\ge1}f_{jj}^{(n)}$ and the mean recurrence time $m_{jj}=\sum_{n\ge1}n f_{jj}^{(n)}\in[0,\infty]$;
--   4. irreducibility: for every pair of states $(i,j)$ there is an $n$ with $p_{ij}^{(n)}>0$;
--   5. aperiodicity: for every state $k$ the greatest common divisor of $\{n\ge1: p_{kk}^{(n)}>0\}$ is $1$;
--   6. positive recurrence: every state $j$ has $f_{jj}=1$ and $m_{jj}<\infty$;
--   7. stationary distributions: probability vectors $\pi$ with $\pi=\pi P$, that is $\pi_j\ge0$, $\sum_j\pi_j=1$ and $\pi_j=\sum_i\pi_i p_{ij}$ for all $j$.
--
--   These are the notions in terms of which Theorems 1.1 and 1.2 of the book are stated.
--
--   **Formalization Note** The return probability and the mean recurrence time are valued in $[0,\infty]$ so that $m_{jj}=\infty$ (null recurrence) is representable. Irreducibility is the per-pair reading ("for each pair $(i,j)$ there is an $n$"); the book's sentence on p.37 can be read literally as one $n$ for all pairs, which is not the intended notion. The gcd condition is stated as "every common divisor of the return times equals 1".
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.26–38, §1.9.2 (transition matrix, Eq. (1.21), irreducibility and period p.37, f_jj and m_jj pp.37–38)

import Mathlib

open scoped ENNReal

namespace QueueingFundamentals.Foundations

/-- A homogeneous discrete-parameter Markov chain on the states `{0, 1, 2, …}`, given by its
transition matrix `P = {p_ij}` (Gross et al., §1.9.2, p.26): every entry is nonnegative and every
row sums to one. -/
structure TransitionMatrix where
  /-- `p i j = Pr{X_n = j | X_{n-1} = i}`. -/
  p : ℕ → ℕ → ℝ
  nonneg : ∀ i j, 0 ≤ p i j
  row_sum : ∀ i, HasSum (fun j => p i j) 1

namespace TransitionMatrix

variable (P : TransitionMatrix)

/-- The `m`-step transition probabilities `p_ij^(m)`, built from `P^(m) = P · P^(m-1)`
(Eq. (1.21)) with `P^(0)` the identity matrix. -/
noncomputable def stepProb : ℕ → ℕ → ℕ → ℝ
  | 0, i, j => if i = j then 1 else 0
  | n + 1, i, j => ∑' k, P.p i k * stepProb n k j

/-- First-passage probabilities `f_ij^(n)` (p.37–38): the probability that the chain started in
`i` enters `j` for the first time at step `n` (for `i = j`: returns to `j` for the first time at
step `n`). By convention `f_ij^(0) = 0`; `f_ij^(1) = p_ij`, and
`f_ij^(n+1) = ∑_{k ≠ j} p_ik f_kj^(n)`. -/
noncomputable def firstPassage : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | 1, i, j => P.p i j
  | n + 2, i, j => ∑' k, if k = j then 0 else P.p i k * firstPassage (n + 1) k j

/-- `f_jj = ∑_{n ≥ 1} f_jj^(n)`, the probability of ever returning to `j` (p.37),
as an extended nonnegative real. -/
noncomputable def returnProb (j : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (P.firstPassage n j j)

/-- The mean recurrence time `m_jj = ∑_{n ≥ 1} n f_jj^(n)` (p.38), valued in `[0, ∞]` so that
`m_jj = ∞` is representable. -/
noncomputable def meanRecurrenceTime (j : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (P.firstPassage n j j)

/-- Irreducibility (p.37): every pair of states communicates, i.e. for every pair `(i, j)` there
is an `n` with `p_ij^(n) > 0`. -/
def Irreducible : Prop :=
  ∀ i j : ℕ, ∃ n : ℕ, 0 < P.stepProb n i j

/-- A state `k` is aperiodic (p.37) when the greatest common divisor of the return times
`{n ≥ 1 : p_kk^(n) > 0}` is `1`, i.e. `1` is the only common divisor of these times. -/
def AperiodicState (k : ℕ) : Prop :=
  ∀ d : ℕ, (∀ n : ℕ, 0 < n → 0 < P.stepProb n k k → d ∣ n) → d = 1

/-- The chain is aperiodic when each of its states is aperiodic (p.37). -/
def Aperiodic : Prop :=
  ∀ k : ℕ, P.AperiodicState k

/-- A state `j` is positive recurrent (p.38) when it is recurrent (`f_jj = 1`) and its mean
recurrence time is finite (`m_jj < ∞`). -/
def PositiveRecurrentState (j : ℕ) : Prop :=
  P.returnProb j = 1 ∧ P.meanRecurrenceTime j < ⊤

/-- The chain is positive recurrent when every state is positive recurrent. -/
def PositiveRecurrent : Prop :=
  ∀ j : ℕ, P.PositiveRecurrentState j

/-- `π` is a solution of the stationary equations `π = πP`, `πe = 1` (Theorem 1.1) that is a
probability vector: `π_j ≥ 0`, `∑_j π_j = 1` and `π_j = ∑_i π_i p_ij` for every `j`. -/
def IsStationaryDist (π : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ π j) ∧ HasSum π 1 ∧ ∀ j, HasSum (fun i => π i * P.p i j) (π j)

end TransitionMatrix

end QueueingFundamentals.Foundations


