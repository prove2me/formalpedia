-- Prove2me | Definitions.Def_SortingCounterexamples_Optimal_Protocol
-- name    : SortingCounterexamples_Optimal_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:10.909911+00:00
-- url     : https://prove2.me/theorems/966b0ec9-d3ff-4f79-88d0-4b0877b77089
-- title:
--   §1 — rankings, counterexamples, learners, adaptive oracles, query count and lie budget
-- statement:
--   This file fixes the interaction model of *ranking from counterexamples* (§1, p. 1).
--
--   1. **Rankings.** The items are $[n]$, written $0,\dots,n-1$. A ranking $\pi$ is a permutation listing the items by position; $\pi$ places $i$ **before** $j$ when $\pi^{-1}(i)<\pi^{-1}(j)$.
--   2. **Counterexamples.** A counterexample is an unordered pair $\{i,j\}$ of two distinct items (a two-element set). It is **truthful** for a query $\pi$ and a target $\sigma$ when $\pi$ and $\sigma$ disagree on the relative order of $i$ and $j$, and **untruthful** otherwise.
--   3. **Learners and oracles.** A transcript is the chronological list of past queries, each with the pair returned to it. A deterministic learner maps a transcript to its next ranking; it sees neither the target nor the lie budget. An oracle maps a transcript and the current query either to *approval* or to a counterexample pair.
--   4. **Run and query count.** Starting from the empty transcript, each round appends the learner's query and the returned pair, until the oracle approves. The query count $Q\in\{1,2,\dots\}\cup\{\infty\}$ is the number of queries up to and including the approved one, and $Q=\infty$ when approval never occurs.
--   5. **Lie budget.** For a target $\sigma$, an oracle is *run-admissible* for a learner with budget $k$ if every transcript of their run contains at most $k$ untruthful counterexamples. An oracle is *admissible* (a valid oracle) for $\sigma$ and $k$ if it is run-admissible against every deterministic learner, i.e. against every sequence of queries.
--   6. **Randomized learners.** A randomized learner is a family $(L_\omega)_{\omega\in\Omega}$ of deterministic learners indexed by a seed of a probability space $(\Omega,\mu)$, such that every decision $\omega\mapsto L_\omega(h)$ is measurable. Its expected query count against an oracle is $\int Q(L_\omega,O)\,d\mu(\omega)$ in $[0,\infty]$.
--   7. **Rate.** $f(n,k)=n\log n+nk$ with the natural logarithm.
--
--   These objects are used by the goal theorem and by Theorem 4.5.
--
--   **Formalization Note** Items are `Fin n` and rankings `Equiv.Perm (Fin n)` read as position $\mapsto$ item. The query count is in `ℕ∞` (an infimum over the approval times, `⊤` when there is none). Pairs are two-element `Finset`s, so an oracle cannot transmit an orientation. A randomized learner draws its whole seed at the start; since histories are finite and the seed space is arbitrary, this covers learners with arbitrary private randomness and memory.
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed p. 1 / PDF p. 2, §1 'Ranking from counterexamples' (model, truthful/untruthful pairs, lie budget k unknown to the learner, worst-case expected number of queries for randomized learners); printed p. 19 / PDF p. 20, Theorem 4.5 (n ≥ 2, k ≥ 0)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace SortingCounterexamples.Optimal

/-- A ranking (linear order) of the items `Fin n`, listed by position:
`π a` is the item at position `a` (position `0` is first). -/
abbrev Ranking (n : ℕ) := Equiv.Perm (Fin n)

/-- Item `i` is placed before item `j` in the ranking `π`. -/
def Ranking.Before {n : ℕ} (π : Ranking n) (i j : Fin n) : Prop :=
  π.symm i < π.symm j

instance {n : ℕ} (π : Ranking n) (i j : Fin n) : Decidable (π.Before i j) :=
  inferInstanceAs (Decidable (π.symm i < π.symm j))

/-- An unordered pair `{i, j}` of two distinct items: the counterexample format. -/
abbrev ItemPair (n : ℕ) := {s : Finset (Fin n) // s.card = 2}

/-- The counterexample `s` returned on query `π` is *truthful* for the target `σ` when `π`
and `σ` disagree on the relative order of the two items of `s`. -/
def Truthful {n : ℕ} (π σ : Ranking n) (s : ItemPair n) : Prop :=
  ∃ i ∈ s.1, ∃ j ∈ s.1, π.Before i j ∧ σ.Before j i

/-- The visible history: the past queries, each with the counterexample returned to it,
in chronological order. -/
abbrev Transcript (n : ℕ) := List (Ranking n × ItemPair n)

/-- A deterministic proper learner: its next query is a ranking chosen from the history.
It receives neither the target nor the lie budget. -/
abbrev DetLearner (n : ℕ) := Transcript n → Ranking n

/-- An adaptive oracle: given the history and the current query it either approves
(`none`) or returns a counterexample pair (`some s`). -/
abbrev Oracle (n : ℕ) := Transcript n → Ranking n → Option (ItemPair n)

/-- `run L O t` is the transcript of the first `t` rounds of the interaction of `L` with `O`
when none of them was approved, and `none` once an approval has occurred. -/
def run {n : ℕ} (L : DetLearner n) (O : Oracle n) : ℕ → Option (Transcript n)
  | 0 => some []
  | t + 1 => (run L O t).bind fun h => (O h (L h)).map fun s => h ++ [(L h, s)]

/-- The number of queries up to and including the first approved one;
`⊤` when the oracle never approves. -/
noncomputable def queries {n : ℕ} (L : DetLearner n) (O : Oracle n) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : run L O t = none), (t : ℕ∞)

/-- The number of untruthful counterexamples, for the target `σ`, in a transcript. -/
noncomputable def lieCount {n : ℕ} (σ : Ranking n) (h : Transcript n) : ℕ := by
  classical
  exact h.countP fun e => decide (¬ Truthful e.1 σ e.2)

/-- Along the run of `L` against `O`, at most `k` counterexamples are untruthful for `σ`. -/
def RunAdmissible {n : ℕ} (L : DetLearner n) (O : Oracle n) (σ : Ranking n) (k : ℕ) : Prop :=
  ∀ (t : ℕ) (h : Transcript n), run L O t = some h → lieCount σ h ≤ k

/-- The oracle `O` is a valid oracle for target `σ` with lie budget `k`: against every
sequence of queries (every deterministic learner) it returns at most `k` untruthful
counterexamples. -/
def Admissible {n : ℕ} (O : Oracle n) (σ : Ranking n) (k : ℕ) : Prop :=
  ∀ L : DetLearner n, RunAdmissible L O σ k

/-- A randomized proper learner given by a random seed `ω` of an arbitrary probability
space: with seed `ω` it acts as the deterministic learner `L ω`. Each decision is a random
variable. -/
def IsRandomizedLearner {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (L : Ω → DetLearner n) :
    Prop :=
  ∀ (h : Transcript n) (π : Ranking n), MeasurableSet {ω | L ω h = π}

/-- The rate `n log n + n k` (natural logarithm). -/
noncomputable def rate (n k : ℕ) : ℝ := n * Real.log n + n * k

end SortingCounterexamples.Optimal


