-- Prove2me | Definitions.Def_ConnectedFVS_General_FiniteGraphs
-- name    : ConnectedFVS_General_FiniteGraphs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T17:17:30.625897+00:00
-- url     : https://prove2.me/theorems/b4c64dc3-185c-403a-892d-d6266c14cf83
-- title:
--   Finite undirected and directed graphs
-- statement:
--   An undirected graph has vertices $\{0,\ldots,n-1\}$ for an arbitrary natural number $n$, and a symmetric Boolean adjacency matrix with false diagonal. Its associated Mathlib simple graph has exactly those edges. A directed graph has the same unrestricted finite vertex labeling and an arbitrary Boolean arc matrix, allowing opposite arcs and self-arcs. Labels represent every finite graph up to relabeling. There is no connectedness, planarity, minor-exclusion or treewidth assumption.
-- source:
--   Misra et al., FPT-Algorithms for Connected Feedback Vertex Set, arXiv:0909.3180v1 (17 September 2009), §2–§3, PDF pp. 3–4

import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace ConnectedFVS.General

/-- Every finite simple undirected graph is represented by relabeling its vertices. -/
structure FiniteUGraph where
  n : ℕ
  edge : Fin n → Fin n → Bool
  symmetric : ∀ u v, edge u v = edge v u
  loopless : ∀ u, edge u u = false

def FiniteUGraph.graph (G : FiniteUGraph) : SimpleGraph (Fin G.n) where
  Adj u v := G.edge u v = true
  symm := ⟨by intro u v h; rw [← G.symmetric u v]; exact h⟩
  loopless := ⟨by intro u h; simp [G.loopless u] at h⟩

/-- Finite directed adjacency, allowing both arc orientations and self-arcs.
Self-arcs cannot occur in a selected out-tree. -/
structure FiniteDGraph where
  n : ℕ
  arc : Fin n → Fin n → Bool

end ConnectedFVS.General


