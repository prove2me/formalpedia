-- Prove2me | Definitions.Def_ZhangTangLabelCut_LP2_FiniteGraph
-- name    : ZhangTangLabelCut_LP2_FiniteGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:11:22.51101+00:00
-- url     : https://prove2.me/theorems/9241ec55-9e9e-4390-aba9-9042865096db
-- title:
--   Finite graphs and simple terminal paths
-- statement:
--   A finite graph consists of finite vertex and edge types, a tail and a head for each edge, and a choice of directed or undirected traversal. Each edge is counted once even when it can be traversed in either direction. Simplicity means no loops and no two edges with the same endpoints (up to reversal in the undirected case).
--
--   A simple path from $s$ to $t$ is an injective sequence of vertices, beginning at $s$ and ending at $t$, together with an edge joining each consecutive pair in the permitted direction. The general graph object permits loops and parallel edges; the simple-graph predicate excludes them for the gap witnesses. Length-zero paths are allowed precisely when the endpoints coincide.
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), p. 2, Definition 1.1; p. 6, definition of simple terminal paths

import Mathlib

namespace ZhangTangLabelCut.LP2

/-- A finite graph with named edges; `directed = false` permits traversal both ways. -/
structure FiniteGraph where
  V : Type
  E : Type
  finiteV : Fintype V
  finiteE : Fintype E
  tail : E → V
  head : E → V
  directed : Bool

attribute [instance] FiniteGraph.finiteV FiniteGraph.finiteE

/-- Traversal of one named edge. -/
def FiniteGraph.Step (G : FiniteGraph) (e : G.E) (u v : G.V) : Prop :=
  (G.tail e = u ∧ G.head e = v) ∨
    (G.directed = false ∧ G.head e = u ∧ G.tail e = v)

/-- No loops or parallel edges; undirected endpoints are compared in both orders. -/
def FiniteGraph.Simple (G : FiniteGraph) : Prop :=
  (∀ e, G.tail e ≠ G.head e) ∧
  ∀ e f, ((G.tail e = G.tail f ∧ G.head e = G.head f) ∨
    (G.directed = false ∧ G.tail e = G.head f ∧ G.head e = G.tail f)) → e = f

/-- Simple paths carry an injective vertex sequence and its actual edges. -/
structure Path (G : FiniteGraph) (s t : G.V) where
  length : ℕ
  vertex : Fin (length + 1) → G.V
  edge : Fin length → G.E
  start : vertex 0 = s
  finish : vertex (Fin.last length) = t
  simple : Function.Injective vertex
  step : ∀ j, G.Step (edge j) (vertex j.castSucc) (vertex j.succ)

end ZhangTangLabelCut.LP2


