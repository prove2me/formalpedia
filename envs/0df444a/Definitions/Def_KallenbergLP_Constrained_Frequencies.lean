-- Prove2me | Definitions.Def_KallenbergLP_Constrained_Frequencies
-- name    : KallenbergLP_Constrained_Frequencies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:29.815263+00:00
-- url     : https://prove2.me/theorems/59cf7d20-b7c7-46e5-8cc5-9ca5f2bab759
-- title:
--   Expected state-action frequencies, their limit points, policy classes and the polytope X (Kallenberg §4.7.2)
-- statement:
--   This file fixes the objects of Section 4.7.2 of Kallenberg's *Linear Programming and Finite Markovian Control Problems*, on top of the finite stationary Markov decision model $M$: a finite state set $E$, for each state $i$ a finite nonempty set $A(i)$ of admissible actions, rewards $r_{ia}$ and transition probabilities $p_{iaj}\ge 0$ with $\sum_j p_{iaj}=1$.
--
--   **Policies.** A policy $R$ is history-dependent and randomized: at each decision epoch it chooses an action in $A(i_t)$ with a probability that may depend on the whole past history and the current state. Under $R$ started in state $i$, $\mathbb P_R(X_t=j,\ Y_t=a\mid X_1=i)$ is the probability that the state at time $t$ is $j$ and the action chosen is $a$; it is a finite sum over histories of products of decision-rule and transition probabilities. The classes are:
--
--   1. $C$, all policies;
--   2. $C_M$, Markov (memoryless) policies, whose decision rule at time $t$ ignores the past;
--   3. $C_S$, stationary policies $\pi^\infty$, which use one decision rule $\pi$ ($\pi_{ia}\ge0$, $\sum_{a\in A(i)}\pi_{ia}=1$) at every epoch;
--   4. $C_D$, pure stationary policies $f^\infty$, $f(i)\in A(i)$.
--
--   **Frequencies.** For an initial distribution $\beta$ and $T\ge1$, the expected state-action frequencies in the first $T$ periods are (4.7.1)
--
--   $$x^T_{ja}(R)=\frac1T\sum_{t=1}^T\sum_i\beta_i\,\mathbb P_R(X_t=j,\ Y_t=a\mid X_1=i),\qquad a\in A(j),\ j\in E.$$
--
--   $X(R)$ is the set of all limit points (limits of convergent subsequences) of $\{x^T(R)\}_{T\ge1}$, $C_1=\{R\in C: |X(R)|=1\}$, and for a class $C'$ the set $L(C')=\{x\in X(R): R\in C'\}$; this gives $L$, $L(M)$, $L(C)$ (for $C_1$), $L(S)$ and $L(D)$.
--
--   **Stationary frequencies.** $P(\pi)_{ij}=\sum_a p_{iaj}\pi_{ia}$, $P^*(\pi)$ is its stationary matrix, the Cesàro limit of $P(\pi)^n$, and (4.7.2)
--
--   $$x_{ja}(\pi)=[\beta^TP^*(\pi)]_j\,\pi_{ja}.$$
--
--   **The polytope.** $X$ is the set of $x$ for which some $y$ makes $(x,y)$ feasible for the linear system (4.7.7):
--
--   $$\sum_i\sum_a(\delta_{ij}-p_{iaj})x_{ia}=0,\qquad \sum_a x_{ja}+\sum_i\sum_a(\delta_{ij}-p_{iaj})y_{ia}=\beta_j\quad(j\in E),\qquad x,y\ge0.$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The model is the platform's `StationaryMDP` (actions in a common finite type, admissible sets per state) with its history-dependent randomized policies `AvgHRPolicy`; frequency vectors are indexed by the admissible pairs `Pair M`. Time starts at $0$ in Lean, so `prob R k i p` is the book's $\mathbb P_R(X_{k+1}=j, Y_{k+1}=a\mid X_1=i)$. Policy classes are predicates on `AvgHRPolicy` that constrain only the weights of admissible actions. $P^*$ is defined by `limUnder` of the Cesàro means $\frac1n\sum_{k=1}^nP^k$; that this limit exists is Theorem 2.4.1(i) of the book.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 19–23, Section 2.2; p. 29, Theorem 2.4.1(i) and Definition 2.4.2; pp. 134–135, (4.7.1)–(4.7.2); p. 138, (4.7.7)–(4.7.8)

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_AverageLP_Model

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses Filter Topology

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- `occ R k t h s p`: the probability, under the policy `R` started at decision epoch `t` after
the history `h` of past state-action pairs in the current state `s`, that the state and the
action `k` epochs later are `p = (j, a)`.  Computed as a finite sum over histories. -/
noncomputable def occ {M : StationaryMDP S A} (R : AvgHRPolicy M) :
    ℕ → ℕ → List (S × A) → S → KallenbergLP.AverageLP.Pair M → ℝ
  | 0, t, h, s, p => if p.1.1 = s then R.q t h s p.1.2 else 0
  | (k + 1), t, h, s, p =>
      ∑ b ∈ M.admissible s, R.q t h s b *
        ∑ s', M.trans s b s' * occ R k (t + 1) (h ++ [(s, b)]) s' p

/-- `prob R k i p = ℙ_R(X_{k+1} = j, Y_{k+1} = a | X_1 = i)` for `p = (j, a)`: the book's time
`t = k + 1` (time starts at 1 in the book, at 0 here).  Kallenberg (1983), §2.2, p. 20. -/
noncomputable def prob {M : StationaryMDP S A} (R : AvgHRPolicy M) (k : ℕ) (i : S) (p : KallenbergLP.AverageLP.Pair M) : ℝ :=
  occ R k 0 [] i p

/-- The expected state-action frequencies in the first `T` periods, (4.7.1):
`x^T_{ja}(R) = (1/T) ∑_{t=1}^T ∑_i β_i ℙ_R(X_t = j, Y_t = a | X_1 = i)`.
Kallenberg (1983), p. 134, (4.7.1).  (At `T = 0` the value is `0`; it plays no role in the
limit points.) -/
noncomputable def freq {M : StationaryMDP S A} (β : S → ℝ) (R : AvgHRPolicy M) (T : ℕ)
    (p : KallenbergLP.AverageLP.Pair M) : ℝ :=
  (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ∑ i, β i * prob R k i p

/-- `X(R)`: the set of all limit points of the vectors `{x^T(R), T = 1, 2, …}`, i.e. the limits
of convergent subsequences.  Kallenberg (1983), p. 134. -/
def limitPoints {M : StationaryMDP S A} (β : S → ℝ) (R : AvgHRPolicy M) : Set (KallenbergLP.AverageLP.Pair M → ℝ) :=
  {x | ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => freq β R (φ n)) atTop (𝓝 x)}

/-- `C_M`: memoryless (Markov) policies — the decision rule at epoch `t` does not depend on the
past history.  Kallenberg (1983), §2.2, p. 20. -/
def IsMarkov {M : StationaryMDP S A} (R : AvgHRPolicy M) : Prop :=
  ∀ t h h' s a, a ∈ M.admissible s → R.q t h s a = R.q t h' s a

/-- A stationary decision rule `π`: `π_{ia} ≥ 0` and `∑_{a ∈ A(i)} π_{ia} = 1` for every `i`.
The set of these is a product of simplices.  Kallenberg (1983), §2.2, p. 20. -/
def StatRule (M : StationaryMDP S A) : Set (KallenbergLP.AverageLP.Pair M → ℝ) :=
  {π | (∀ p, 0 ≤ π p) ∧ ∀ s, ∑ a ∈ (M.admissible s).attach, π ⟨(s, a.1), a.2⟩ = 1}

/-- `C_S`: stationary policies `π^∞` — the same decision rule `π` at every epoch, whatever the
history.  Kallenberg (1983), §2.2, p. 20. -/
def IsStationary {M : StationaryMDP S A} (R : AvgHRPolicy M) : Prop :=
  ∃ π ∈ StatRule M, ∀ t h s a (ha : a ∈ M.admissible s), R.q t h s a = π ⟨(s, a), ha⟩

/-- A pure decision rule `f`, `f(i) ∈ A(i)`.  The set of these is finite. -/
abbrev PureRule (M : StationaryMDP S A) := (s : S) → M.admissible s

/-- `C_D`: pure stationary policies `f^∞`.  Kallenberg (1983), §2.2, p. 20. -/
def IsPureStationary {M : StationaryMDP S A} (R : AvgHRPolicy M) : Prop :=
  ∃ f : PureRule M, ∀ t h s a, a ∈ M.admissible s →
    R.q t h s a = if a = (f s).1 then 1 else 0

/-- `C_1 = {R ∈ C | |X(R)| = 1}`.  Kallenberg (1983), p. 135. -/
def IsC1 {M : StationaryMDP S A} (β : S → ℝ) (R : AvgHRPolicy M) : Prop :=
  ∃ x, limitPoints β R = {x}

/-- `L(C') := {x(R) ∈ X(R) | R ∈ C'}` for a policy class `C'` (given as a predicate).  With
`C' = C, C_M, C_1, C_S, C_D` this is `L, L(M), L(C), L(S), L(D)` of p. 135. -/
def Lset (M : StationaryMDP S A) (β : S → ℝ) (C' : AvgHRPolicy M → Prop) : Set (KallenbergLP.AverageLP.Pair M → ℝ) :=
  {x | ∃ R, C' R ∧ x ∈ limitPoints β R}

/-- The stationary policy `π^∞` of a decision rule `π ∈ StatRule M`. -/
noncomputable def StatRule.toPolicy {M : StationaryMDP S A} (π : KallenbergLP.AverageLP.Pair M → ℝ)
    (hπ : π ∈ StatRule M) : AvgHRPolicy M where
  q := fun _ _ s a => if ha : a ∈ M.admissible s then π ⟨(s, a), ha⟩ else 0
  nonneg := by
    intro t h s a
    by_cases ha : a ∈ M.admissible s
    · simp only [ha, dite_true]; exact hπ.1 _
    · simp [ha]
  sum_one := by
    intro t h s
    rw [← hπ.2 s, ← Finset.sum_attach (M.admissible s)]
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [a.2]

/-- The weights `f_{ia} = 1` if `a = f(i)`, `0` otherwise, of a pure decision rule. -/
def pureWeights {M : StationaryMDP S A} (f : PureRule M) : KallenbergLP.AverageLP.Pair M → ℝ :=
  fun p => if p.1.2 = (f p.1.1).1 then 1 else 0

/-- The pure stationary policy `f^∞`. -/
noncomputable def pureStationaryPolicy {M : StationaryMDP S A} (f : PureRule M) : AvgHRPolicy M :=
  stationaryPolicy M (fun s => (f s).1) (fun s => (f s).2)

/-- `P(π)_{ij} = ∑_{a ∈ A(i)} p_{iaj} π_{ia}`.  Kallenberg (1983), p. 21. -/
def policyMatrix {M : StationaryMDP S A} (π : KallenbergLP.AverageLP.Pair M → ℝ) : Matrix S S ℝ :=
  fun i j => ∑ a ∈ (M.admissible i).attach, π ⟨(i, a.1), a.2⟩ * M.trans i a.1 j

/-- The stationary matrix `P* = (C) lim_{n→∞} P^n`, the Cesàro limit
`lim_n (1/n) ∑_{k=1}^n P^k`.  Kallenberg (1983), Theorem 2.4.1(i) and Definition 2.4.2, p. 29.
(Its existence is Theorem 2.4.1(i); `limUnder` picks the limit.) -/
noncomputable def stationaryMatrix (P : Matrix S S ℝ) : Matrix S S ℝ :=
  limUnder atTop (fun n : ℕ => (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, P ^ (k + 1))

/-- (4.7.2): `x_{ja}(π) := [β^T P*(π)]_j · π_{ja}`.  Kallenberg (1983), p. 135. -/
noncomputable def xStat {M : StationaryMDP S A} (β : S → ℝ) (π : KallenbergLP.AverageLP.Pair M → ℝ) : KallenbergLP.AverageLP.Pair M → ℝ :=
  fun p => (∑ i, β i * stationaryMatrix (policyMatrix π) i p.1.1) * π p

/-- The linear system (4.7.7):
`∑_i ∑_a (δ_{ij} − p_{iaj}) x_{ia} = 0`, `∑_a x_{ja} + ∑_i ∑_a (δ_{ij} − p_{iaj}) y_{ia} = β_j`
for `j ∈ E`, and `x, y ≥ 0`.  Kallenberg (1983), p. 138. -/
def IsFeasible477 (M : StationaryMDP S A) (β : S → ℝ) (x y : KallenbergLP.AverageLP.Pair M → ℝ) : Prop :=
  (∀ p, 0 ≤ x p) ∧ (∀ p, 0 ≤ y p) ∧
  (∀ j, ∑ p : KallenbergLP.AverageLP.Pair M, ((if p.1.1 = j then 1 else 0) - M.trans p.1.1 p.1.2 j) * x p = 0) ∧
  (∀ j, ∑ p : KallenbergLP.AverageLP.Pair M, (if p.1.1 = j then x p else 0) +
      ∑ p : KallenbergLP.AverageLP.Pair M, ((if p.1.1 = j then 1 else 0) - M.trans p.1.1 p.1.2 j) * y p = β j)

/-- (4.7.8): `X := {x | there exists a y such that (x, y) is feasible for (4.7.7)}`.
Kallenberg (1983), p. 138. -/
def polytopeX (M : StationaryMDP S A) (β : S → ℝ) : Set (KallenbergLP.AverageLP.Pair M → ℝ) :=
  {x | ∃ y, IsFeasible477 M β x y}

end KallenbergLP.Constrained


