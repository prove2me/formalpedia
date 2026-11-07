-- Prove2me | Definitions.Def_IncrementalER_Edge
-- name    : IncrementalER_Edge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:12.125696+00:00
-- url     : https://prove2.me/theorems/aed1acdc-a1ff-490d-be31-8cc589d2b74a
-- title:
--   Capacitated multigraphs on $n$ vertices as edge lists; components and feasible demands
-- statement:
--   A capacitated multigraph on the vertex set $\{0,\dots,n-1\}$ is a finite list of edges $e=(u_e,v_e,c_e)$; parallel edges are separate entries. Its Laplacian is
--
--   $$L_G=\sum_{e}c_e(\mathbf 1_{u_e}-\mathbf 1_{v_e})(\mathbf 1_{u_e}-\mathbf 1_{v_e})^\top .$$
--
--   The connected components of $G$ are those of the simple graph in which $x\sim y$ iff $x\neq y$ and some edge joins $x$ and $y$; a vertex without such an edge is a component of its own. A demand $d\in\mathbb R^n$ is **componentwise feasible** if $d^\top\mathbf 1_C=0$ for every connected component $C$. A sparse demand is given as a list of (vertex, value) pairs, and its dense vector adds the values listed for each vertex.
--
--   These are the graphs and demands of Theorem 1.1 and of its footnote 1.
--
--   **Formalization Note** A loop $u_e=v_e$ is allowed; it contributes $0$ to $L_G$ and nothing to connectivity.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), §1, p.3 (Laplacian); Theorem 1.1 and footnote 1, p.4; §3, p.10 (multigraphs)

import Mathlib

open Matrix

namespace IncrementalER

/-!
# Capacitated multigraphs on `Fin n` given by edge lists

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), §1, p.3 (the Laplacian
`L_G := ∑_{(u,v)∈E} c(u,v)(1u − 1v)(1u − 1v)⊤`), Theorem 1.1 and footnote 1, p.4, and §3, p.10
(undirected capacitated multigraphs).

**Formalization Note.**
* A multigraph is a list of edges; parallel edges are separate list entries and their Laplacian
  terms add. A loop `u = v` is allowed and contributes `0` to the Laplacian and nothing to the
  connectivity graph (a generalization: the paper's edges join two vertices).
* The connected components are those of the simple graph on `Fin n` in which `x ~ y` iff some
  edge joins `x ≠ y`. A vertex without such an edge is its own component, so a componentwise
  feasible demand vanishes there.
* Sparse vectors are lists of (vertex, value) pairs; their dense form adds the values listed for a
  vertex (with distinct vertices, the listed value).
-/

/-- An edge `(u, v)` with capacity `c`. -/
structure Edge (n : ℕ) where
  /-- one endpoint -/
  u : Fin n
  /-- the other endpoint -/
  v : Fin n
  /-- the capacity (conductance) -/
  c : ℝ

/-- The incidence vector `1u − 1v` of an edge. -/
def Edge.incVec {n : ℕ} (e : Edge n) : Fin n → ℝ :=
  Pi.single e.u 1 - Pi.single e.v 1

/-- The Laplacian `L_G = ∑_{e=(u,v)} c_e (1u − 1v)(1u − 1v)⊤` of the multigraph with edge list
`es` (p.3). -/
noncomputable def edgeLap {n : ℕ} (es : List (Edge n)) : Matrix (Fin n) (Fin n) ℝ :=
  (es.map fun e => e.c • Matrix.vecMulVec e.incVec e.incVec).sum

/-- The simple graph of the multigraph: `x ~ y` iff `x ≠ y` and some edge joins them. -/
def edgeGraph {n : ℕ} (es : List (Edge n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y => ∃ e ∈ es, e.u = x ∧ e.v = y

open Classical in
/-- `d` sums to zero on every connected component `C` of the multigraph, `d⊤1_C = 0`
(footnote 1, p.4). Vertices without an incident non-loop edge are their own components. -/
def ComponentFeasible {n : ℕ} (es : List (Edge n)) (d : Fin n → ℝ) : Prop :=
  ∀ C : (edgeGraph es).ConnectedComponent,
    ∑ x ∈ Finset.univ.filter (fun x => (edgeGraph es).connectedComponentMk x = C), d x = 0

/-- The dense vector `d ∈ ℝ^{Fin n}` of a sparse list of (vertex, value) pairs. -/
def sparseVec {n : ℕ} (l : List (Fin n × ℝ)) : Fin n → ℝ :=
  fun x => (l.map fun p => if p.1 = x then p.2 else 0).sum

end IncrementalER


