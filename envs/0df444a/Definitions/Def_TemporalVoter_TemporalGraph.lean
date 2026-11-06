-- Prove2me | Definitions.Def_TemporalVoter_TemporalGraph
-- name    : TemporalVoter_TemporalGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:20.180326+00:00
-- url     : https://prove2.me/theorems/ab3f1f61-be1b-4379-94d0-462d94e8f576
-- title:
--   Temporal graph with fixed degrees; volume $\mathrm{Vol}(S)$, edge count $m$, minimum degree $d_{\min}$, cut size $e_t(S,\overline S)$
-- statement:
--   A **temporal graph with fixed degrees** on a finite vertex set $V$ is a sequence $\mathcal G=(G_t:t\ge0)$ of simple undirected graphs on $V$ such that the degree of each vertex $v$ in $G_t$ does not depend on $t$. This common degree is denoted $d(v)$, and no vertex is isolated: $d(v)\ge1$ for all $v$.
--
--   For such a graph and a vertex set $S\subseteq V$ we use:
--
--   1. the **volume** $\mathrm{Vol}(S)=\sum_{v\in S}d(v)$;
--   2. the **number of edges** $m=\tfrac12\sum_{v\in V}d(v)$, which does not depend on $t$;
--   3. the **minimum degree** $d_{\min}=\min_{v\in V}d(v)$;
--   4. the **cut size** $e_t(S,\overline S)$, the number of edges of $G_t$ joining $S$ to its complement $\overline S=V\setminus S$.
--
--   Fixed degrees make the volume of a set time-invariant, while the edges crossing a cut may change at every step. All conductances and the voter model of the mission are built on these quantities.
--
--   **Formalization Note** The degree function $d$ is part of the data, together with the hypothesis that it is the degree of $v$ in every snapshot $G_t$. The minimum degree is an infimum over $V$, which is the minimum for nonempty $V$. The cut size reuses the published `SpectralSparsify.Decomp.cutEdges`, which counts ordered pairs $(s,w)\in S\times\overline S$ with $s\sim w$, i.e. each crossing edge once. Adjacency is decided classically.
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Definition 1.1, p.5; §1.3, (1), p.5 and p.6

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_cutEdges

open scoped Classical

namespace TemporalVoter

/-- **Temporal graph with fixed degrees** (Rocha Avila, Dell, Lapinskas, *Temporal Conductance and
Bounds on the Voter Model for Dynamic Networks*, arXiv:2606.13374, version of 2 Nov 2026,
Definition 1.1, p.5): a sequence `(G t : t ≥ 0)` of simple undirected graphs on a common finite
vertex set `V` in which the degree of every vertex `v` in `G t` is a number `d v` that does not
depend on `t`, and `d v ≥ 1` for every `v` (no isolated vertices).

**Formalization Note** The common degree `d` is carried as data together with the hypothesis
`degree_eq` that it is the degree of `v` in every snapshot; the vertex set is a `Fintype`
("n-vertex", p.7). Decidability of adjacency is classical. -/
structure TemporalGraph (V : Type) [Fintype V] where
  /-- The graph `G_t` at time `t`. -/
  G : ℕ → SimpleGraph V
  /-- The time-independent degree `d(v)`. -/
  d : V → ℕ
  /-- The degree of `v` in `G_t` is `d(v)` for every time `t`. -/
  degree_eq : ∀ t v, (G t).degree v = d v
  /-- No isolated vertices: `d(v) ≥ 1`. -/
  one_le_d : ∀ v, 1 ≤ d v

namespace TemporalGraph

variable {V : Type} [Fintype V]

/-- The volume `Vol(S) = ∑_{v ∈ S} d(v)` of a vertex set (§1.3, (1), p.5). -/
noncomputable def vol (T : TemporalGraph V) (S : Finset V) : ℝ :=
  ∑ v ∈ S, (T.d v : ℝ)

/-- The number of edges `m = ½ ∑_v d(v)` of the temporal graph (Definition 1.1, p.5). -/
noncomputable def m (T : TemporalGraph V) : ℝ :=
  (∑ v, (T.d v : ℝ)) / 2

/-- The minimum degree `d_min = min_v d(v)` (p.7).

**Formalization Note** `⨅` over a finite nonempty index is the minimum; on the empty vertex type it
is `0` (no statement of the mission is affected: there every vertex set is empty). -/
noncomputable def dmin (T : TemporalGraph V) : ℝ :=
  ⨅ v, (T.d v : ℝ)

/-- `e_t(S, S̄)`, the number of edges of `G_t` between `S` and its complement (§1.3, p.6),
via the published `SpectralSparsify.Decomp.cutEdges`. -/
noncomputable def cut (T : TemporalGraph V) (t : ℕ) (S : Finset V) : ℝ :=
  (SpectralSparsify.Decomp.cutEdges (T.G t) S Sᶜ : ℝ)

end TemporalGraph

end TemporalVoter


