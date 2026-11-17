-- Prove2me | Definitions.Def_TemporalAgg_Supplement_selState
-- name    : TemporalAgg_Supplement_selState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:17:26.844142+00:00
-- url     : https://prove2.me/theorems/67377dc5-bbb6-45cf-98e9-e2df78376b33
-- title:
--   The adaptive temporal-selection process on random walks (Theorem 1.3)
-- statement:
--   The process of Theorem 1.3 runs on the vertex set $[n]$ and is driven by a deterministic adaptive adversarial **strategy** $\sigma$, which fixes an initial simple graph $G_1$ and two rules. At each time $t=1,2,\dots$:
--
--   1. seeing the whole history (for every vertex, its walk if sampled so far), the strategy names a set of vertices; each named vertex $v$ whose walk has not been sampled before gets its walk now: a random walk of length $\ell$ from $v$ in the current graph $G_t$, with fresh randomness;
--   2. seeing the history including these walks, the strategy deletes a set of edges, giving $G_{t+1}\subseteq G_t$.
--
--   So $G_1\supseteq G_2\supseteq\cdots$, every vertex is the source of at most one walk, sampled once, at an adaptively chosen time $t(v)$ in $G_{t(v)}$. The **congestion** of an edge $e$ at time $T$ is the total number of traversals of $e$ by all walks sampled at times $\le T$.
--
--   The probability law is realized by drawing, for every vertex $v$, independent uniform numbers $\xi_{v,1},\dots,\xi_{v,\ell}\in\{0,\dots,n!-1\}$ that drive the walk from $v$ (see the random-walk definition). Since the walk from $v$ is sampled at most once and the history before its sampling depends only on other vertices' numbers, the walk from $v$ is, given the history, a fresh random walk in the current graph, as in the paper. The graph of time step $t\ge1$ is the graph stored in the state at the end of step $t-1$.
--
--   **Formalization Note** Requests to sample an already-sampled vertex are ignored. The strategy's information is the list of observations at the ends of the previous steps; because the strategy is deterministic this determines the graphs and sampling times, so it is the whole history.
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), §1.3, p.6 (Theorem 1.3); App. A, pp.35–36 (proof, Algorithm 4); §2.1, p.15

import Mathlib
import Definitions.Def_TemporalAgg_Supplement_walkPath

namespace TemporalAgg.Supplement

/-! The adaptive temporal-selection process of Theorem 1.3 (Haeupler, Paramonov, *Temporal
Aggregation: Maintaining Randomness against Adaptive Adversaries*, STOC 2027 submission,
manuscript of 2026-11-03, sha256 42ebf866…, §1.3 p.6, proof in App. A pp.35–36).

An adaptive adversary produces graphs `G₁ ⊇ G₂ ⊇ ⋯` on the vertex set `Fin n` (edge deletions
only) and samples, for each vertex `v`, at most one random walk of length `ℓ` from `v`, in the graph
`G_{t(v)}` current at the adaptively chosen time `t(v)`. -/

/-- What the adversary has observed at the end of a time step: for every vertex `v`, the walk from
`v` (as its vertex list) if it has been sampled so far, `none` otherwise. -/
abbrev SelObs (n : ℕ) := Fin n → Option (List (Fin n))

/-- A deterministic adaptive adversarial strategy for temporal selection.
* `G₁` is the initial graph.
* At time `t ≥ 1`, seeing the history `h` (the observations at the end of steps `1, …, t−1`, a list
  of length `t − 1`), the adversary asks for the walks from the vertices `sample h` to be sampled
  now.
* After the walks of time `t` are drawn, seeing the history extended by step `t`, it deletes the
  edges `delete h'`, which gives the next graph `G_{t+1}`.

**Formalization Note** The history determines the graphs and sampling times (the strategy is
deterministic), so the observations are the whole history. The strategy never sees walk
randomness of walks not yet sampled. -/
structure SelStrategy (n : ℕ) where
  G₁ : SimpleGraph (Fin n)
  sample : List (SelObs n) → Finset (Fin n)
  delete : List (SelObs n) → Set (Sym2 (Fin n))

/-- State of the process at the end of a time step: the graph for the next step, and the history
of observations. -/
structure SelState (n : ℕ) where
  graph : SimpleGraph (Fin n)
  hist : List (SelObs n)

/-- The current observation (no walk sampled yet before step 1). -/
def SelState.cur {n : ℕ} (s : SelState n) : SelObs n :=
  s.hist.getLastD (fun _ => none)

/-- One time step of the temporal-selection process. Starting from `s` (whose graph is the current
graph `G_t`), the vertices requested by the strategy that have not been sampled before get their
walk, a walk of length `ℓ` in `G_t` driven by the numbers `ξ v`; then the strategy deletes edges.

**Formalization Note** Requests for already-sampled vertices are ignored, so every vertex is the
source of at most one walk, sampled once. Graphs only shrink (`deleteEdges`). -/
noncomputable def selStep {n : ℕ} (σ : SelStrategy n) (ℓ : ℕ) (ξ : Fin n → Fin ℓ → ℕ)
    (s : SelState n) : SelState n := by
  classical
  exact
    let cur := s.cur
    let R := (σ.sample s.hist).filter (fun v => cur v = none)
    let o : SelObs n := fun v =>
      if v ∈ R then some (walkPath s.graph v (List.ofFn (ξ v))) else cur v
    let h := s.hist ++ [o]
    ⟨s.graph.deleteEdges (σ.delete h), h⟩

/-- **The temporal-selection process.** `selState σ ℓ ξ t` is the state at the end of time step `t`
(`t = 0`: before any step, graph `G₁`, empty history). Its graph is `G_{t+1}`, so the graph of
time step `t ≥ 1` is `(selState σ ℓ ξ (t − 1)).graph`.

**Formalization Note** (probabilistic model) The walk from `v` is driven by `ξ v : Fin ℓ → ℕ`. With
`ξ` uniform on `Fin n → Fin ℓ → Fin n!` (independent uniform numbers), and since the walk from
`v` is sampled at most once and the history before its sampling depends only on other vertices'
numbers, the walk from `v` is, given the history, a fresh random walk of length `ℓ` from `v` in the
current graph (`walkStep`). This realizes the law of the paper's process. -/
noncomputable def selState {n : ℕ} (σ : SelStrategy n) (ℓ : ℕ) (ξ : Fin n → Fin ℓ → ℕ) :
    ℕ → SelState n
  | 0 => ⟨σ.G₁, []⟩
  | t + 1 => selStep σ ℓ ξ (selState σ ℓ ξ t)

/-- Congestion of the edge `e` at time `t`: the number of traversals of `e`, with multiplicity, by
all walks sampled at times `≤ t`. -/
noncomputable def selCongestion {n : ℕ} (σ : SelStrategy n) (ℓ : ℕ) (ξ : Fin n → Fin ℓ → ℕ)
    (t : ℕ) (e : Sym2 (Fin n)) : ℕ :=
  ∑ v, match (selState σ ℓ ξ t).cur v with
    | some w => edgeTraversals w e
    | none => 0

end TemporalAgg.Supplement


