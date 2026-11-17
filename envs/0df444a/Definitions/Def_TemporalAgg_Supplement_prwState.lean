-- Prove2me | Definitions.Def_TemporalAgg_Supplement_prwState
-- name    : TemporalAgg_Supplement_prwState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:17:56.577285+00:00
-- url     : https://prove2.me/theorems/59c3dc5b-c8fc-4932-8f77-18c83d7ac091
-- title:
--   Random walks maintained by proactive resampling against edge deletions (Theorem 1.4)
-- statement:
--   The process of Theorem 1.4 has a simple graph $G$ on $[n]$, a set of **sources** (each the source of one walk of length $\ell$), and a deterministic adaptive adversarial strategy that only deletes edges.
--
--   * **Time 0.** The walk of every source is sampled in $G$. This sampling is neither adversarial nor algorithmic and starts no resampling schedule.
--   * **Time $t\ge1$.** Seeing the whole history (the walk configurations at the ends of steps $0,\dots,t-1$), the strategy deletes a set of edges, $G_t\subseteq G_{t-1}$. Every current walk that traverses a deleted edge of $G_{t-1}$ is resampled in $G_t$; this is an **adversarial sample** at time $t$. Then **proactive resampling** resamples in $G_t$ every walk that had an adversarial sample at some time $s<t$ with $t=s+2^i$, $i\ge0$.
--
--   Every resample is a fresh random walk of length $\ell$ from the source in the current graph. The **congestion** of an edge $e$ at time $t$ is the number of traversals of $e$ by the current walks at the end of step $t$.
--
--   The law is realized by independent uniform numbers $\xi_{v,t,i}\in\{0,\dots,n!-1\}$ driving the sample of the walk from $v$ at time $t$; the expectation at time $t$ is over the numbers of times $0,\dots,t$.
--
--   **Formalization Note** A walk that is both forced and proactively resampled at the same time step is drawn once (two successive fresh draws in the same graph have the law of one).
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), §1.2, p.3; §1.3, p.5 (proactive resampling) and p.6 (Theorem 1.4); App. A, p.37 (order of operations within a step)

import Mathlib
import Definitions.Def_TemporalAgg_Supplement_walkPath
import Definitions.Def_TemporalAgg_Supplement_ProactiveDue

namespace TemporalAgg.Supplement

/-! Random walks maintained by proactive resampling against adaptive edge deletions (Theorem 1.4 of
Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries*,
STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, §1.2 p.3, §1.3 pp.5–6, proof in
App. A p.37). -/

/-- The current walks: the vertex list of the walk from every vertex (meaningful for sources). -/
abbrev WalkConfig (n : ℕ) := Fin n → List (Fin n)

/-- A deterministic adaptive adversary that only deletes edges: at time `t ≥ 1`, seeing the history
`h` (the walk configurations at the end of steps `0, …, t−1`, a list of length `t`), it deletes the
edges `delete h`. -/
structure DeletionStrategy (n : ℕ) where
  delete : List (WalkConfig n) → Set (Sym2 (Fin n))

/-- State at the end of a time step: current graph `G_t`, current walks, the adversarial sample
times of every walk so far, and the history of walk configurations. -/
structure PRWState (n : ℕ) where
  graph : SimpleGraph (Fin n)
  walks : WalkConfig n
  adv : Fin n → Finset ℕ
  hist : List (WalkConfig n)

/-- Time 0: every source's walk of length `ℓ` is sampled in `G`, driven by `ξ v 0`. This sampling
is neither adversarial nor algorithmic, so it starts no proactive schedule. Non-sources carry the
trivial walk `[v]` (no edges). -/
noncomputable def prwInit {n : ℕ} (G : SimpleGraph (Fin n)) (src : Finset (Fin n)) (ℓ : ℕ)
    (ξ : Fin n → ℕ → Fin ℓ → ℕ) : PRWState n := by
  classical
  exact
    let w : WalkConfig n := fun v =>
      if v ∈ src then walkPath G v (List.ofFn (ξ v 0)) else [v]
    ⟨G, w, fun _ => ∅, [w]⟩

/-- One time step `t ≥ 1` (p.3, p.5, and the order fixed on p.37): the strategy deletes edges
(`G_t = G_{t−1}` minus them); every source walk traversing a deleted edge of `G_{t−1}` is resampled
(an adversarial sample at time `t`); then proactive resampling resamples every source walk with an
adversarial sample at some `s < t` with `t = s + 2ⁱ`. All resamples are fresh walks of length `ℓ`
from the source in `G_t`, driven by `ξ v t`.

**Formalization Note** A walk that is both forced and proactively resampled at time `t` is drawn
once (two successive fresh draws in the same graph have the same law as one). -/
noncomputable def prwStep {n : ℕ} (src : Finset (Fin n)) (ℓ : ℕ) (σ : DeletionStrategy n)
    (ξ : Fin n → ℕ → Fin ℓ → ℕ) (t : ℕ) (s : PRWState n) : PRWState n := by
  classical
  exact
    let D := σ.delete s.hist
    let G' := s.graph.deleteEdges D
    let forced : Fin n → Prop := fun v =>
      v ∈ src ∧ ∃ e ∈ walkEdges (s.walks v), e ∈ D ∧ e ∈ s.graph.edgeSet
    let adv' : Fin n → Finset ℕ := fun v => if forced v then insert t (s.adv v) else s.adv v
    let res : Fin n → Prop := fun v => forced v ∨ (v ∈ src ∧ ProactiveDue (s.adv v) t)
    let w' : WalkConfig n := fun v =>
      if res v then walkPath G' v (List.ofFn (ξ v t)) else s.walks v
    ⟨G', w', adv', s.hist ++ [w']⟩

/-- **Walks maintained by proactive resampling.** `prwState G src ℓ σ ξ t` is the state at the end of
time step `t`, for the initial graph `G`, the set `src` of sources (each the source of one walk of
length `ℓ`), and the edge-deleting strategy `σ`.

**Formalization Note** (probabilistic model) The sample of the walk from `v` at time `t` is driven by
`ξ v t`; with all `ξ v t i` independent uniform on `Fin n!`, every resample is, given the history, a
fresh random walk in the current graph (`walkStep`), as in the paper. -/
noncomputable def prwState {n : ℕ} (G : SimpleGraph (Fin n)) (src : Finset (Fin n)) (ℓ : ℕ)
    (σ : DeletionStrategy n) (ξ : Fin n → ℕ → Fin ℓ → ℕ) : ℕ → PRWState n
  | 0 => prwInit G src ℓ ξ
  | t + 1 => prwStep src ℓ σ ξ (t + 1) (prwState G src ℓ σ ξ t)

/-- Congestion of `e` at the end of time step `t`: traversals of `e`, with multiplicity, by the
current walks of all sources. -/
noncomputable def prwCongestion {n : ℕ} (G : SimpleGraph (Fin n)) (src : Finset (Fin n)) (ℓ : ℕ)
    (σ : DeletionStrategy n) (ξ : Fin n → ℕ → Fin ℓ → ℕ) (t : ℕ) (e : Sym2 (Fin n)) : ℕ :=
  ∑ v ∈ src, edgeTraversals ((prwState G src ℓ σ ξ t).walks v) e

/-- The randomness of the first `t + 1` time steps, `η v s i ∈ Fin n!` for `s ≤ t`, extended by `0`
to all times (the process up to time `t` reads only times `≤ t`). -/
def prwRand {n ℓ t : ℕ} (η : Fin n → Fin (t + 1) → Fin ℓ → Fin (Nat.factorial n)) :
    Fin n → ℕ → Fin ℓ → ℕ :=
  fun v s i => if h : s < t + 1 then (η v ⟨s, h⟩ i : ℕ) else 0

end TemporalAgg.Supplement


