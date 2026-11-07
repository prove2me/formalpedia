-- Prove2me | Definitions.Def_DynOracleConn_GraphAfter
-- name    : DynOracleConn_GraphAfter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:46:18.03197+00:00
-- url     : https://prove2.me/theorems/633d8d8d-ff32-4756-9e64-8430a3f54baf
-- title:
--   The graph after $k$ updates, and forest sequences
-- statement:
--   Let $\sigma$ be a sequence of edge updates of a simple undirected graph on $[n]$ that starts with no edges. $G_k(\sigma)$ is the graph after the first $k$ updates, with $G_0(\sigma)$ empty. The sequence is a **forest sequence** when $G_k(\sigma)$ is acyclic for every $0\le k\le|\sigma|$. This is the meaning of "the graph is a forest throughout the entire stream" in Theorem 4.
--
--   **Formalization Note** Updates and validity of a sequence are the published `PunctSketch.Update` and `PunctSketch.IsValidStream`, which have the same meaning as here: an insertion adds an absent edge between two distinct vertices, and a deletion removes a present edge.
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4; §2, p.16; Theorem 4, p.7

import Mathlib
import Definitions.Def_PunctSketch_Update
import Definitions.Def_PunctSketch_IsValidStream

namespace DynOracleConn

/-!
# The graph after `k` updates, and forest sequences

Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4 and the box
"Dynamic s-t Connectivity", §2, p.16: "The input is a simple undirected graph on the fixed vertex
set [n], initially with no edges"; "Updates. Edge insertions and deletions in G."

**Formalization Note.** Updates and validity are the published general objects:
`PunctSketch.Update n` (an edge of `Fin n` and an insert/delete bit, applied by
`PunctSketch.Update.apply`) and `PunctSketch.IsValidStream` (each update has two distinct endpoints,
an insertion adds an absent edge, a deletion removes a present one, from the empty graph).
`graphAfter σ k` is the graph after the first `k` updates, so `graphAfter σ 0 = ⊥`.
`ForestThroughout σ` says that the graph is a forest at every prefix, including the empty start and
the end ("the graph is a forest throughout the entire stream", Theorem 4, p.7).
-/

/-- The graph after the first `k` updates of `σ`, starting from the empty graph. -/
noncomputable def graphAfter {n : ℕ} (σ : List (PunctSketch.Update n)) (k : ℕ) : SimpleGraph (Fin n) :=
  PunctSketch.streamGraph (σ.take k)

/-- The graph is a forest after every prefix of `σ` (including the empty prefix and `σ` itself). -/
def ForestThroughout {n : ℕ} (σ : List (PunctSketch.Update n)) : Prop :=
  ∀ k ≤ σ.length, (graphAfter σ k).IsAcyclic

end DynOracleConn


