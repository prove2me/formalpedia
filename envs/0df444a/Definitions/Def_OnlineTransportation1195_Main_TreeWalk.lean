-- Prove2me | Definitions.Def_OnlineTransportation1195_Main_TreeWalk
-- name    : OnlineTransportation1195_Main_TreeWalk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:34:34.862351+00:00
-- url     : https://prove2.me/theorems/6ce99397-425d-4a52-828c-260d3acb4532
-- title:
--   Finite rooted-tree walks, first traversals, DFS and deadline costs
-- statement:
--   Use the general positive weighted-tree record from the referenced library: a root, a parent map, ordinary combinatorial depths, and a positive real weight on each non-root edge. The edge is labeled by its endpoint further from the root; the root pseudo-edge is excluded. No HST condition is used.
--
--   A walk is a finite adjacent-vertex list whose first vertex is the root. The list containing just the root represents a walk with no traversals. First traversal of an edge requires an actual occurrence, with no earlier crossing. Downward prefix cost charges movement away from the root and charges zero upward; total prefix weight charges both directions. Both include the traversal at the end of the prefix.
--
--   $$\sum_{e\in E}w_e/d_e=1$$
--
--   is combined with positive deadlines and their monotonicity along root paths in the normalization predicate. DFS means a closed root-based walk traversing every edge exactly once in each direction, with arbitrary sibling order. Output deadline predicates separately require coverage and a true first traversal. They impose no return-to-root requirement on an output walk.
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), §3, Theorems 1.3/3.1 and fixed DFS, PDF / printed p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree

open scoped BigOperators
open Classical

namespace OnlineTransportation1195.Main

abbrev Tree (n : ℕ) := PolylogKServer.HST.WTree (Fin n)

namespace Tree

variable {n : ℕ} (T : Tree n)

/-- Edges are identified by their endpoint further from the root. -/
def edges : Finset (Fin n) := Finset.univ.erase T.root

def Adj (u v : Fin n) : Prop :=
  (v ≠ T.root ∧ T.parent v = u) ∨ (u ≠ T.root ∧ T.parent u = v)

def vertexAt (L : List (Fin n)) (i : ℕ) : Fin n := L.getD i T.root

/-- Actual adjacent-vertex lists, with the root included as the first vertex.
The singleton list [root] is the empty-edge walk. -/
def Walk (L : List (Fin n)) : Prop :=
  L.head? = some T.root ∧
    ∀ i, i + 1 < L.length → T.Adj (T.vertexAt L i) (T.vertexAt L (i + 1))

def DownAt (L : List (Fin n)) (e : Fin n) (i : ℕ) : Prop :=
  e ≠ T.root ∧ i + 1 < L.length ∧ T.vertexAt L i = T.parent e ∧ T.vertexAt L (i + 1) = e

def UpAt (L : List (Fin n)) (e : Fin n) (i : ℕ) : Prop :=
  e ≠ T.root ∧ i + 1 < L.length ∧ T.vertexAt L i = e ∧ T.vertexAt L (i + 1) = T.parent e

def CrossAt (L : List (Fin n)) (e : Fin n) (i : ℕ) : Prop :=
  T.DownAt L e i ∨ T.UpAt L e i

def FirstAt (L : List (Fin n)) (e : Fin n) (i : ℕ) : Prop :=
  T.CrossAt L e i ∧ ∀ j, j < i → ¬ T.CrossAt L e j

def Covers (L : List (Fin n)) : Prop :=
  ∀ e ∈ T.edges, ∃ i, T.CrossAt L e i

/-- Upward traversals cost zero in §3; the root pseudo-edge is ignored. -/
noncomputable def downStep (u v : Fin n) : ℝ :=
  if v ≠ T.root ∧ T.parent v = u then T.W v else 0

/-- Both directions are charged in Theorem 1.3. -/
noncomputable def totalStep (u v : Fin n) : ℝ :=
  if v ≠ T.root ∧ T.parent v = u then T.W v
  else if u ≠ T.root ∧ T.parent u = v then T.W u else 0

/-- Cost through traversal i, inclusive. -/
noncomputable def downPrefix (L : List (Fin n)) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (i + 1), T.downStep (T.vertexAt L j) (T.vertexAt L (j + 1))

noncomputable def totalPrefix (L : List (Fin n)) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (i + 1), T.totalStep (T.vertexAt L j) (T.vertexAt L (j + 1))

/-- These predicates require a real first visit, rather than giving an unvisited
edge a time of zero. No return to the root is imposed on the output walk. -/
def DownDeadlines (L : List (Fin n)) (d : Fin n → ℝ) : Prop :=
  T.Walk L ∧ T.Covers L ∧ ∀ e ∈ T.edges,
    ∃ i, T.FirstAt L e i ∧ T.downPrefix L i ≤ d e

def TotalDeadlines (L : List (Fin n)) (d : Fin n → ℝ) : Prop :=
  T.Walk L ∧ T.Covers L ∧ ∀ e ∈ T.edges,
    ∃ i, T.FirstAt L e i ∧ T.totalPrefix L i ≤ d e

/-- An Euler tour of a tree with every edge used once in each direction is
precisely a root-based depth-first tour, with an arbitrary order of siblings. -/
def DFS (L : List (Fin n)) : Prop :=
  T.Walk L ∧ L.getLast? = some T.root ∧
    ∀ e ∈ T.edges,
      (Finset.univ.filter (fun i : Fin L.length => T.DownAt L e i)).card = 1 ∧
      (Finset.univ.filter (fun i : Fin L.length => T.UpAt L e i)).card = 1

def Monotone (d : Fin n → ℝ) : Prop :=
  ∀ a ∈ T.edges, ∀ b ∈ T.edges, T.IsAnc a b → d a ≤ d b

def Normalized (d : Fin n → ℝ) : Prop :=
  (∀ e ∈ T.edges, 0 < d e) ∧ T.Monotone d ∧ ∑ e ∈ T.edges, T.W e / d e = 1

def Unequal (d : Fin n → ℝ) : Prop :=
  ∃ e ∈ T.edges, ∃ f ∈ T.edges, d e ≠ d f

end Tree
end OnlineTransportation1195.Main


