-- Prove2me | Definitions.Def_DetCCHard_SrcGraph
-- name    : DetCCHard_SrcGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:08.163494+00:00
-- url     : https://prove2.me/theorems/f476ee1f-b5c6-47ac-be75-6fea844c6bac
-- title:
--   Source multigraphs and the YES/NO coloring promises
-- statement:
--   A **source graph** $G = (V, E)$ has vertices $\{0, \dots, n-1\}$ and a list of edge occurrences (pairs of endpoints; parallel edges are separate occurrences). The **degree** of a vertex is the number of edge occurrences meeting it. $G$ has the **shape of Theorem 5.2** with degree bound $\Delta$ if it has at least one edge, no loops, no isolated vertices and maximum degree at most $\Delta$.
--
--   $G$ is a **YES graph** if it is 3-colorable: some $c : V \to [3]$ gives the endpoints of every edge occurrence different colors. $G$ is a **NO graph with gap $\gamma$** if every $c : V \to [3]$ has at least $\gamma|E|$ monochromatic edge occurrences.
--
--   These are the promises produced by the coloring source (Theorem 5.2) and consumed by the collision lemma (Lemma 6.3) and the gap tables (Theorem 8.4).
--
--   **Formalization Note** Edges are stored as ordered pairs; orientation is never used. Edge occurrences are counted with multiplicity (§G.1, p.71).
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 5.2, pp.16–17, and §G.1, p.71

import Mathlib

namespace DetCCHard

/-- A **source multigraph** `G = (V, E)` (Gaspers–He–Mackenzie, arXiv:2508.05597, held version
sha256 ad552d13…a4a03, Theorem 5.2, pp.16–17, and §G.1, p.71): `n` vertices `0, …, n − 1` and a
list of edge occurrences, each an (unordered) pair of endpoints.

**Formalization Note** Edges are stored as ordered pairs in a list; the orientation is never used,
and parallel edges are separate occurrences counted with multiplicity (§G.1, p.71). -/
structure SrcGraph where
  /-- the number of vertices `n = |V|` -/
  n : ℕ
  /-- the edge occurrences -/
  edges : List (Fin n × Fin n)

namespace SrcGraph

/-- The **degree** of a vertex: the number of edge occurrences meeting it (a loop would count
twice; source graphs are loopless). -/
def deg (G : SrcGraph) (v : Fin G.n) : ℕ :=
  (G.edges.filter (fun e => e.1 = v)).length + (G.edges.filter (fun e => e.2 = v)).length

end SrcGraph

/-- The **shape of a source graph** in Theorem 5.2 (p.16): a nonempty loopless multigraph with no
isolated vertices and maximum degree at most `Δ` ("nonempty" means at least one edge, §G.1,
p.71: "add a disjoint edge, so that the graph is nonempty"). -/
def IsShape (Δ : ℕ) (G : SrcGraph) : Prop :=
  G.edges ≠ [] ∧ (∀ e ∈ G.edges, e.1 ≠ e.2) ∧ (∀ v, 1 ≤ G.deg v) ∧ ∀ v, G.deg v ≤ Δ

/-- A **YES graph** (Theorem 5.2, item 1, p.16): `G` is 3-colorable, i.e. some coloring
`c : V → [3]` gives the two endpoints of every edge occurrence different colors. -/
def IsYes (G : SrcGraph) : Prop :=
  ∃ c : Fin G.n → Fin 3, ∀ e ∈ G.edges, c e.1 ≠ c e.2

/-- A **NO graph with gap `γ`** (Theorem 5.2, item 2, p.17): every 3-coloring of `G` has at least
`γ|E|` monochromatic edge occurrences. -/
def IsNo (γ : ℚ) (G : SrcGraph) : Prop :=
  ∀ c : Fin G.n → Fin 3,
    γ * G.edges.length ≤ ((G.edges.filter (fun e => c e.1 = c e.2)).length : ℚ)

end DetCCHard


