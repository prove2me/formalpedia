-- Prove2me | Definitions.Def_DisjointPathsDAG_Supplement_Undirected
-- name    : DisjointPathsDAG_Supplement_Undirected
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:59:45.863978+00:00
-- url     : https://prove2.me/theorems/0fbed652-6353-4649-8441-fd6eeb61690f
-- title:
--   Undirected graphs with integer weights: paths, two disjoint shortest paths, and the word-weight input
-- statement:
--   An **undirected multigraph** with vertex set $\{0,\dots,n-1\}$ and edge set $\{0,\dots,m-1\}$ assigns to every edge $e$ two ends $u_e, v_e$; parallel edges and self-loops are allowed. An edge can be crossed in either direction. An **undirected $s$–$t$ path** is a sequence of edges $e_1,\dots,e_\ell$ together with a traversal $s=x_0,x_1,\dots,x_\ell=t$ in which $e_j$ joins $x_{j-1}$ and $x_j$, and no vertex repeats; for $s=t$ the empty sequence is the zero-edge path $(s)$.
--
--   Edge weights are natural numbers $w(e)$, and the weight of a path is the sum of the weights of its edges. A **shortest undirected $s$–$t$ path** has least weight among all undirected $s$–$t$ paths. For terminal pairs $(s_1,t_1),\dots,(s_k,t_k)$, a **$k$-DSP solution** consists of shortest undirected $s_i$–$t_i$ paths $P_i$ whose vertex sets are pairwise disjoint; the instance is **feasible** when a solution exists.
--
--   The input of an instance lists, as machine words, $n$, $m$, the terminals $s_1,t_1,\dots$, the two ends of every edge, and then the weights $w(0),\dots,w(m-1)$; no real numbers and no field elements are input. This is the computational model of the undirected case of Theorem 5.12, where weights are positive integers stored in words.
--
--   **Formalization Note** The graph reuses `DisjointPathsDAG.Digraph`, with `tail`/`head` read as the two ends. A traversal is a list of arcs `(e, b)`: `b = false` crosses `e` from `tail e` to `head e`, `b = true` the other way; it must be a path of the generic `IsPathOf` (consecutive, no repeated vertex). Positivity and boundedness of weights are hypotheses of the theorem, not of these definitions. Outputs are decoded with `DisjointPathsDAG.decodePaths`.
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 2, p.6 (paths; Section 2.1, the word-weight model) and Theorem 5.12, p.33

import Mathlib
import Definitions.Def_DisjointPathsDAG_Graph
import Definitions.Def_DisjointPathsDAG_Machine
import Definitions.Def_DisjointPathsDAG_Encoding

set_option autoImplicit false

namespace DisjointPathsDAG.Supplement

/-!
# Undirected graphs with positive integer weights: paths, k-DSP solutions, input layout

Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 2, p.6 ("A path contains its endpoints
and repeats no vertex; for a vertex v, the zero-edge path (v) is a path from v to v"; Section 2.1:
"the only exception is the undirected case of Theorem 5.12, where the weights are positive integers
bounded by (m+n)O(1) and are stored in words"), and Theorem 5.12, p.33 (the undirected case).

**Formalization Note** This module bundles the undirected layer, whose declarations depend on each
other: arc ends, undirected paths, shortest undirected paths, the k-DSP solution predicate, feasibility,
and the input encoding.
* An undirected multigraph is a `DisjointPathsDAG.Digraph n m` whose `tail`/`head` are read as the two
  ends of each edge; the orientation carries no meaning. Parallel edges and self-loops are allowed (a
  path never uses a self-loop, since it would repeat a vertex).
* An edge `e` is crossed in one of two directions: the arc `(e, false)` goes from `tail e` to `head e`,
  the arc `(e, true)` from `head e` to `tail e`. An undirected `s`–`t` path is a list of edges that
  admits a traversal: a list of arcs forming a path of the generic `IsPathOf` (consecutive, no repeated
  vertex) whose edges are the given list. The empty list is the zero-edge path at `s = t`.
* Weights are naturals (`wt : Fin m → ℕ`); positivity and the polynomial bound are hypotheses of the
  theorem, not of the definitions. Path weights are natural sums.
* Input layout: the words `graphWords G pairs` of `DisjointPathsDAG.Encoding` (with the two ends in
  place of tail and head) followed by the weights `wt 0, …, wt (m − 1)` as words; no real inputs and
  no field inputs. The output convention is that of `DisjointPathsDAG.decodePaths`.
-/

variable {n m k : ℕ}

/-- The start of the arc `a = (e, b)`: `tail e` if `b = false`, `head e` if `b = true`. -/
def arcTail (G : Digraph n m) (a : Fin m × Bool) : Fin n :=
  if a.2 then G.head a.1 else G.tail a.1

/-- The end of the arc `a = (e, b)`: `head e` if `b = false`, `tail e` if `b = true`. -/
def arcHead (G : Digraph n m) (a : Fin m × Bool) : Fin n :=
  if a.2 then G.tail a.1 else G.head a.1

/-- A traversal of an undirected `s`–`t` path: a list of arcs, consecutive from `s` to `t`, repeating
no vertex. -/
def IsUPathArcs (G : Digraph n m) (s t : Fin n) (p : List (Fin m × Bool)) : Prop :=
  IsPathOf (arcTail G) (arcHead G) (fun _ => True) s t p

/-- The vertex set of the traversal `p` started at `s` (both endpoints included). -/
def uVertSet (G : Digraph n m) (s : Fin n) (p : List (Fin m × Bool)) : Finset (Fin n) :=
  (walkVerts (arcHead G) s p).toFinset

/-- The edge list `q` is an undirected `s`–`t` path: some traversal of it is an `s`–`t` path. -/
def IsUPath (G : Digraph n m) (s t : Fin n) (q : List (Fin m)) : Prop :=
  ∃ p : List (Fin m × Bool), p.map Prod.fst = q ∧ IsUPathArcs G s t p

/-- The weight of an edge list: the natural sum of its edge weights. -/
def uPathWeight (wt : Fin m → ℕ) (q : List (Fin m)) : ℕ := (q.map wt).sum

/-- `q` is a shortest undirected `s`–`t` path: an undirected `s`–`t` path of least weight among all
undirected `s`–`t` paths. -/
def IsUShortest (G : Digraph n m) (wt : Fin m → ℕ) (s t : Fin n) (q : List (Fin m)) : Prop :=
  IsUPath G s t q ∧ ∀ q', IsUPath G s t q' → uPathWeight wt q ≤ uPathWeight wt q'

/-- An undirected k-DSP solution: edge lists `Q i`, each a shortest undirected `sᵢ`–`tᵢ` path, with
traversals `A i` whose vertex sets are pairwise disjoint. -/
def IsUDSPSolution (G : Digraph n m) (wt : Fin m → ℕ) (pairs : Fin k → Fin n × Fin n)
    (Q : Fin k → List (Fin m)) : Prop :=
  (∀ i, IsUShortest G wt (pairs i).1 (pairs i).2 (Q i)) ∧
  ∃ A : Fin k → List (Fin m × Bool),
    (∀ i, (A i).map Prod.fst = Q i ∧ IsUPathArcs G (pairs i).1 (pairs i).2 (A i)) ∧
    ∀ i j, i ≠ j → Disjoint (uVertSet G (pairs i).1 (A i)) (uVertSet G (pairs j).1 (A j))

/-- The undirected k-DSP instance is feasible. -/
def UDSPFeasible (G : Digraph n m) (wt : Fin m → ℕ) (pairs : Fin k → Fin n × Fin n) : Prop :=
  ∃ Q, IsUDSPSolution G wt pairs Q

/-- The input of an undirected k-DSP instance with word-stored integer weights: the graph words
followed by the weights as words; no real and no field inputs. -/
def encodeUDSP (F : Type) (G : Digraph n m) (wt : Fin m → ℕ) (pairs : Fin k → Fin n × Fin n) :
    Input F :=
  ⟨graphWords G pairs ++ (List.finRange m).map wt, [], []⟩

end DisjointPathsDAG.Supplement


