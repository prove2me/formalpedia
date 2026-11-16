-- Prove2me | Definitions.Def_InducedExpanderTest989_Structural_Supplement_QueryAlgorithms
-- name    : InducedExpanderTest989_Structural_Supplement_QueryAlgorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:29:53.482331+00:00
-- url     : https://prove2.me/theorems/b574b68a-a84d-4fbd-8137-a810ab07371a
-- title:
--   Randomized adaptive adjacency-list algorithms with unrestricted computation
-- statement:
--   In the adjacency-list model a graph on $[n]$ with degree bound $d$ is accessed through queries $(v,i)\in[n]\times[d]$, each returning the $i$-th neighbour of $v$ or the null symbol $\bot$. An adaptive algorithm with unrestricted computation is described by a **strategy**: an arbitrary map from transcripts (finite lists of queries with their answers) to the next move, which is either a query $(v,i)$ or a halt with output accept or reject. Run on an adjacency list $O$, a strategy starts from the empty transcript, appends the answer of each query, and stops when it halts. Its **query count** $Q(s,O)\in\{0,1,2,\dots\}\cup\{\infty\}$ is the number of queries before halting, and $\infty$ if it never halts.
--
--   A **randomized** algorithm $\mathcal A$ is a probability law on strategies. Its acceptance probability on $O$ is the probability that the run halts with accept, and its expected query count is
--   $$\mathbb E_{s\sim\mathcal A}\big[Q(s,O)\big]\in[0,\infty].$$
--   $\mathcal A$ is a **correct tester** for a pair of classes (YES, NO) if, on every simple graph $G$ on $[n]$ of maximum degree at most $d$ and every valid adjacency-list ordering $O$ of $G$, it accepts with probability at least $2/3$ when $G$ is a YES graph and accepts with probability at most $1/3$ when $G$ is a NO graph.
--
--   This is the algorithm class over which the lower bounds of Theorems 6.1 and 7.1 quantify.
--
--   **Formalization Note** Strategies are arbitrary functions `QHistory n d → QAction n d`, carrying the product σ-algebra over the countable set of transcripts; a randomized algorithm is a `ProbabilityMeasure` on them. Every algorithm that uses a random seed, including free uniform vertex samples, pushes forward to such a law, so no separate sampling primitive is charged. Rejection with probability at least $2/3$ is read as acceptance probability at most $1/3$: a run that never halts does not accept. Query counts take values in `ℕ∞`.
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.2 (PDF p.4), §1.1 query model; p.34 (PDF p.36), Theorem 6.1; pp.47–48 (PDF pp.49–50), Theorem 7.1

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Graph

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural.Supplement

open MeasureTheory

/-- The next move of an algorithm in the adjacency-list model (§1.1): the query `(v, i)`, or
stop with output `b` (`true` = accept). -/
inductive QAction (n d : ℕ) : Type
  | query : Fin n → Fin d → QAction n d
  | halt : Bool → QAction n d

instance (n d : ℕ) : MeasurableSpace (QAction n d) := ⊤

/-- A transcript: the queries asked so far, each with its answer (`none` is `⊥`). -/
abbrev QHistory (n d : ℕ) := List ((Fin n × Fin d) × Option (Fin n))

/-- A deterministic strategy: an arbitrary map from transcripts to the next move. No
computability, no depth cap. Its σ-algebra is the product σ-algebra over the countably many
transcripts. -/
abbrev QStrategy (n d : ℕ) := QHistory n d → QAction n d

/-- A randomized adaptive algorithm with unrestricted computation: a probability law on
strategies. Any random seed (including free uniform vertex samples) pushes forward to one. -/
abbrev RandAlg (n d : ℕ) := ProbabilityMeasure (QStrategy n d)

/-- The transcript after `k` steps of `s` on the adjacency list `O`; it stops growing once `s`
halts. -/
def histAt {n d : ℕ} (s : QStrategy n d) (O : Oracle n d) : ℕ → QHistory n d
  | 0 => []
  | k + 1 =>
    match s (histAt s O k) with
    | .query v i => histAt s O k ++ [((v, i), O v i)]
    | .halt _ => histAt s O k

/-- `s` halts at step `k`: after `k` answered queries it chooses to stop. -/
def HaltsAt {n d : ℕ} (s : QStrategy n d) (O : Oracle n d) (k : ℕ) : Prop :=
  ∃ b : Bool, s (histAt s O k) = .halt b

/-- The number of adjacency-list queries of the run of `s` on `O` (`⊤` if it never halts). -/
def queryCount {n d : ℕ} (s : QStrategy n d) (O : Oracle n d) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : HaltsAt s O k), (k : ℕ∞)

/-- The run of `s` on `O` halts and accepts. -/
def Accepts {n d : ℕ} (s : QStrategy n d) (O : Oracle n d) : Prop :=
  ∃ k : ℕ, s (histAt s O k) = .halt true

/-- The run of `s` on `O` halts and rejects. -/
def Rejects {n d : ℕ} (s : QStrategy n d) (O : Oracle n d) : Prop :=
  ∃ k : ℕ, s (histAt s O k) = .halt false

/-- Acceptance probability of a randomized algorithm on the adjacency list `O`. -/
def algAcceptProb {n d : ℕ} (A : RandAlg n d) (O : Oracle n d) : ℝ :=
  ((A : Measure (QStrategy n d)) {s | Accepts s O}).toReal

/-- Expected number of adjacency-list queries of `A` on `O`, in `[0, ∞]`. -/
def expectedQueries {n d : ℕ} (A : RandAlg n d) (O : Oracle n d) : ℝ≥0∞ :=
  ∫⁻ s, ((queryCount s O : ℕ∞) : ℝ≥0∞) ∂(A : Measure (QStrategy n d))

/-- `A` accepts every YES graph with probability at least `2/3` and rejects every NO graph with
probability at least `2/3`, read as acceptance probability at most `1/3` (a run that never halts
does not accept), on every simple graph on `[n]` of maximum degree at most `d` and every valid
adjacency-list ordering of it. -/
def IsCorrectTester {n d : ℕ} (A : RandAlg n d) (Yes No : SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ G : SimpleGraph (Fin n), DegreeBound d G → ∀ O : Oracle n d, IsAdjacencyList G O →
    (Yes G → (2/3 : ℝ) ≤ algAcceptProb A O) ∧ (No G → algAcceptProb A O ≤ 1/3)

end InducedExpanderTest989.Structural.Supplement


