-- Prove2me | Definitions.Def_FeedbackSwitching_FeedbackGraph
-- name    : FeedbackSwitching_FeedbackGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:15.650496+00:00
-- url     : https://prove2.me/theorems/f4558aa4-7b8a-4252-9f48-d785cdf4da36
-- title:
--   Feedback graph, observable actions, observing sets and the domination number $\gamma(G)$
-- statement:
--   A **feedback graph** $G=([K],E)$ is a directed graph on the actions $[K]=\{1,\dots,K\}$, possibly with self-loops and with opposite directed edges. Playing action $i$ reveals the loss of every $j$ with $(i,j)\in E$; in particular the incurred loss of $i$ is observed only if $i$ has a self-loop.
--
--   1. An action $i$ is **observable** if $(j,i)\in E$ for some action $j$ (possibly $i$ itself); the graph is **observable** if every action is.
--   2. A set $D\subseteq[K]$ is **observing** if for every $j\in[K]$ there is $s\in D$ with $(s,j)\in E$. A member of $D$ is not counted as observed by itself unless it has a self-loop.
--   3. The **domination number** $\gamma(G)$ is the smallest size of an observing set; it exists exactly when $G$ is observable. Bandit feedback (self-loops only) has $\gamma=K$, and a graph with an action observing all losses has $\gamma=1$.
--
--   These notions decide which of the three regimes of the characterization a graph falls into.
--
--   **Formalization Note** Actions are `Fin K` (Lean action $i$ is the paper's $i+1$); `G i j` means $(i,j)\in E$. $\gamma$ is `sInf` over $\mathbb N$; for a non-observable graph the set is empty and the value $0$ is never read by the mission's statements.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), §3.1–§3.2, p.13 (PDF p.15)

import Mathlib

namespace FeedbackSwitching

/-- **Feedback graph, observability, observing sets, domination number.**
Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…), §3.1–§3.2, p.13 (PDF p.15).

A feedback graph `G = ([K], E)` is a directed graph on the actions, which may contain self-loops and
opposite directed edges. `G i j` means `(i, j) ∈ E`: playing `i` reveals the loss of `j`.

**Formalization Note.** Actions are `Fin K` (Lean action `i` is the paper's action `i + 1`). A
self-loop `G i i` is an ordinary edge: an action observes its own loss only if it has one. -/
abbrev FeedbackGraph (K : ℕ) : Type := Fin K → Fin K → Prop

/-- An action `i` is **observable** if `(j, i) ∈ E` for some action `j` (possibly `i` itself), p.13. -/
def IsObservableAction {K : ℕ} (G : FeedbackGraph K) (i : Fin K) : Prop :=
  ∃ j, G j i

/-- The graph is **observable** if every action is observable, p.13. -/
def Observable {K : ℕ} (G : FeedbackGraph K) : Prop :=
  ∀ i, IsObservableAction G i

/-- A set `D` of actions is **observing** if for every `j ∈ [K]` there is `s ∈ D` with
`(s, j) ∈ E`, p.13. A member of `D` must itself be observed by some member of `D` (with a
self-loop, by itself); membership in `D` does not count as observation. -/
def IsObservingSet {K : ℕ} (G : FeedbackGraph K) (D : Finset (Fin K)) : Prop :=
  ∀ j, ∃ s ∈ D, G s j

/-- The **domination number** `γ(G)`: the smallest size of an observing set, p.13.

**Formalization Note.** `sInf` on `ℕ`; the set is nonempty exactly when `G` is observable (take
`D = univ`), which is the only case in which the paper uses `γ(G)`. For a non-observable graph
the value `sInf ∅ = 0` is a junk value that no statement of the mission reads. -/
noncomputable def dominationNumber {K : ℕ} (G : FeedbackGraph K) : ℕ :=
  sInf {n | ∃ D : Finset (Fin K), IsObservingSet G D ∧ D.card = n}

end FeedbackSwitching


