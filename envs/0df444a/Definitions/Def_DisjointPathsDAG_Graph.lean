-- Prove2me | Definitions.Def_DisjointPathsDAG_Graph
-- name    : DisjointPathsDAG_Graph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:39.458664+00:00
-- url     : https://prove2.me/theorems/837fa40e-279a-439d-bcd9-fafeaa7ef1fa
-- title:
--   Digraphs, paths, k-DP and k-DSP, the polynomial $F$, lightest copies and tight edges
-- statement:
--   A **digraph** $G$ has vertices $0,\dots,n-1$ and edges $0,\dots,m-1$; edge $e$ goes from $\mathrm{tail}(e)$ to $\mathrm{head}(e)$, and parallel edges are allowed. A **path** from $s$ to $t$ in an edge set $H$ is a list of edges of $H$, each starting where the previous one ends, the first at $s$ and the last at $t$, that repeats no vertex; the empty list is the zero-edge path $(s)$, a path from $s$ to $s$ that occupies $s$. Its vertex set contains both endpoints. $G$ is **acyclic** if it has no closed walk of positive length; its numbering is a **topological order** if $\mathrm{tail}(e)<\mathrm{head}(e)$ for every edge.
--
--   Given $k$ terminal pairs $(s_i,t_i)$:
--
--   1. a **k-DP solution** is a tuple $(P_1,\dots,P_k)$ of pairwise vertex-disjoint paths, $P_i$ from $s_i$ to $t_i$;
--   2. with real edge weights $w$ (any sign), a **k-DSP solution** is a k-DP solution in which every $P_i$ is a shortest $s_i$–$t_i$ path of $G$, i.e. $w(P_i)\le w(P')$ for every $s_i$–$t_i$ path $P'$;
--   3. for edge subgraphs $H_1,\dots,H_k$, a solution in $(H_i)$ is a tuple of pairwise vertex-disjoint paths with $P_i$ an $s_i$–$t_i$ path in $H_i$.
--
--   The polynomial of Theorem 4.1 is
--   $$F=\sum_{(P_1,\dots,P_k)}\prod_{i=1}^k\prod_{e\in E(P_i)}x_e\in\mathbb Z[x_e:e\in E],$$
--   the sum over the solutions in $(H_i)$. For the proof of Theorem 4.7 the module also defines the **lightest copies** (one edge of least weight, ties broken by index, per ordered pair of vertices joined by an edge), the distance $d_s(v)=\mathrm{dist}_G(s,v)\in\mathbb R\cup\{+\infty\}$ (the least weight of an $s$–$v$ path, $+\infty$ if none), and the **tight edges** of $s$: the edges $(u,v)$ with $d_s(u)<+\infty$ and $d_s(v)=d_s(u)+w(u,v)$.
--
--   These are the objects of the problems and of the algebraic core of the paper.
--
--   **Formalization Note** Sums over paths range over lists of length at most $n$, which contains every path. Distances take values in `WithTop ℝ`.
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 1, p.2; Section 2, p.6; Theorem 4.1, p.10; proof of Theorem 4.7, p.22

import Mathlib

set_option autoImplicit false

namespace DisjointPathsDAG

open MvPolynomial

/-!
# Graphs, paths, and the disjoint-paths problems

Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 1, p.2 (k-DP and k-DSP), Section 2,
p.6 (paths), Theorem 4.1, p.10 (the polynomial `F`), proof of Theorem 4.7, p.22 (lightest copies,
distances, tight edges).

"In the k vertex-disjoint paths problem (k-DP), the input is a directed graph with n vertices and m
edges and k terminal pairs (si, ti), and the task is to connect every pair by a path so that the paths
are pairwise vertex-disjoint. In the k disjoint shortest paths problem (k-DSP), every path must in
addition be a shortest path between its terminals." "A path contains its endpoints and repeats no
vertex; for a vertex v, the zero-edge path (v) is a path from v to v."

**Formalization Note** This module bundles the graph layer: the generic path predicate, the
digraph, the problems, the polynomial `F` of Theorem 4.1, and the objects of the reduction in the
proof of Theorem 4.7. Vertices are `Fin n`, edges `Fin m` with `tail head : Fin m → Fin n`, so
parallel edges are allowed. A path is the list of its edges together with its start vertex; it is
consecutive and repeats no vertex, and the empty list is the zero-edge path, which requires `s = t`
and occupies `s`. Finite sums over paths range over lists of length at most the number of vertices,
which contains every path, since a path with `ℓ` edges visits `ℓ + 1` distinct vertices.
-/

section Generic

variable {α β : Type}

/-- A walk from `a` to `b` along arcs satisfying `ok`, arc `e` going from `tl e` to `hd e`. The empty
list is the walk from `a` to `a`. -/
def IsWalkOf (tl hd : α → β) (ok : α → Prop) : β → β → List α → Prop
  | a, b, [] => a = b
  | a, b, e :: p => ok e ∧ tl e = a ∧ IsWalkOf tl hd ok (hd e) b p

/-- The vertex sequence of a walk started at `a`: `a` followed by the head of every arc. -/
def walkVerts (hd : α → β) (a : β) (p : List α) : List β := a :: p.map hd

/-- A path from `a` to `b`: a walk that repeats no vertex. -/
def IsPathOf (tl hd : α → β) (ok : α → Prop) (a b : β) (p : List α) : Prop :=
  IsWalkOf tl hd ok a b p ∧ (walkVerts hd a p).Nodup

/-- All lists of length at most `L` over a finite type. -/
noncomputable def listsUpTo (α : Type) [Fintype α] (L : ℕ) : Finset (List α) := by
  classical
  exact (Finset.range (L + 1)).biUnion fun l =>
    Finset.univ.image fun v : List.Vector α l => v.toList

/-- The finite set of all paths from `a` to `b` (every path has at most `card β` arcs). -/
noncomputable def pathsOf [Fintype α] [Fintype β] (tl hd : α → β) (ok : α → Prop) (a b : β) :
    Finset (List α) := by
  classical
  exact (listsUpTo α (Fintype.card β)).filter (IsPathOf tl hd ok a b)

end Generic

/-- A finite directed multigraph with vertices `Fin n` and edges `Fin m`; edge `e` goes from
`tail e` to `head e`. Parallel edges are allowed. -/
structure Digraph (n m : ℕ) where
  tail : Fin m → Fin n
  head : Fin m → Fin n

variable {n m k : ℕ}

namespace Digraph

/-- A walk from `s` to `t` using only edges of the edge set `H`. -/
def IsWalk (G : Digraph n m) (H : Finset (Fin m)) (s t : Fin n) (p : List (Fin m)) : Prop :=
  IsWalkOf G.tail G.head (· ∈ H) s t p

/-- A path from `s` to `t` in the edge-subgraph `H`: consecutive edges of `H`, no repeated vertex. -/
def IsPath (G : Digraph n m) (H : Finset (Fin m)) (s t : Fin n) (p : List (Fin m)) : Prop :=
  IsPathOf G.tail G.head (· ∈ H) s t p

/-- The vertex set of the path `p` started at `s` (it contains both endpoints). -/
def vertSet (G : Digraph n m) (s : Fin n) (p : List (Fin m)) : Finset (Fin n) :=
  (walkVerts G.head s p).toFinset

/-- `G` is acyclic: it has no closed walk of positive length. -/
def IsAcyclic (G : Digraph n m) : Prop :=
  ∀ (v : Fin n) (p : List (Fin m)), G.IsWalk Finset.univ v v p → p = []

/-- The numbering of the vertices is a topological order: every edge goes from a smaller to a
larger vertex. -/
def IsTopo (G : Digraph n m) : Prop :=
  ∀ e : Fin m, G.tail e < G.head e

/-- A solution of the disjoint paths problem in the edge-subgraphs `H i`: for every label `i` a path
`P i` from `(pairs i).1` to `(pairs i).2` in `H i`, the vertex sets pairwise disjoint. -/
def IsSolutionIn (G : Digraph n m) (H : Fin k → Finset (Fin m)) (pairs : Fin k → Fin n × Fin n)
    (P : Fin k → List (Fin m)) : Prop :=
  (∀ i, G.IsPath (H i) (pairs i).1 (pairs i).2 (P i)) ∧
    ∀ i j, i ≠ j → Disjoint (G.vertSet (pairs i).1 (P i)) (G.vertSet (pairs j).1 (P j))

/-- Some solution in the edge-subgraphs `H i` exists. -/
def HasSolution (G : Digraph n m) (H : Fin k → Finset (Fin m)) (pairs : Fin k → Fin n × Fin n) :
    Prop :=
  ∃ P, G.IsSolutionIn H pairs P

/-- `p` is a shortest `s`–`t` path of the edge-subgraph `D` for the weights `wt`. -/
def IsShortestIn (G : Digraph n m) (D : Finset (Fin m)) (wt : Fin m → ℝ) (s t : Fin n)
    (p : List (Fin m)) : Prop :=
  G.IsPath D s t p ∧ ∀ p', G.IsPath D s t p' → (p.map wt).sum ≤ (p'.map wt).sum

end Digraph

/-- The weight of a path: the sum of its edge weights. -/
def pathWeight (wt : Fin m → ℝ) (p : List (Fin m)) : ℝ := (p.map wt).sum

/-- A k-DP solution: pairwise vertex-disjoint paths, `P i` from `sᵢ` to `tᵢ`. -/
def IsDPSolution (G : Digraph n m) (pairs : Fin k → Fin n × Fin n) (P : Fin k → List (Fin m)) :
    Prop :=
  G.IsSolutionIn (fun _ => Finset.univ) pairs P

/-- A k-DSP solution in the edge-subgraph `D`: a k-DP solution in `D` whose every path is a shortest
path of `D` between its terminals. -/
def IsDSPSolutionIn (G : Digraph n m) (D : Finset (Fin m)) (wt : Fin m → ℝ)
    (pairs : Fin k → Fin n × Fin n) (P : Fin k → List (Fin m)) : Prop :=
  G.IsSolutionIn (fun _ => D) pairs P ∧ ∀ i, G.IsShortestIn D wt (pairs i).1 (pairs i).2 (P i)

/-- A k-DSP solution of `G`: pairwise vertex-disjoint paths, each a shortest path of `G`. -/
def IsDSPSolution (G : Digraph n m) (wt : Fin m → ℝ) (pairs : Fin k → Fin n × Fin n)
    (P : Fin k → List (Fin m)) : Prop :=
  IsDSPSolutionIn G Finset.univ wt pairs P

/-- The k-DP instance is feasible. -/
def DPFeasible (G : Digraph n m) (pairs : Fin k → Fin n × Fin n) : Prop :=
  ∃ P, IsDPSolution G pairs P

/-- The k-DSP instance restricted to the edge-subgraph `D` is feasible. -/
def DSPFeasibleIn (G : Digraph n m) (D : Finset (Fin m)) (wt : Fin m → ℝ)
    (pairs : Fin k → Fin n × Fin n) : Prop :=
  ∃ P, IsDSPSolutionIn G D wt pairs P

/-- The k-DSP instance is feasible. -/
def DSPFeasible (G : Digraph n m) (wt : Fin m → ℝ) (pairs : Fin k → Fin n × Fin n) : Prop :=
  DSPFeasibleIn G Finset.univ wt pairs

/-- The setting of Theorem 4.1 (p.10): a digraph, `k` spanning edge-subgraphs, `k` vertex pairs
(`sᵢ = tᵢ` allowed). The topological order is the hypothesis `G.IsTopo`, stated separately. -/
structure Setting (n m k : ℕ) where
  G : Digraph n m
  H : Fin k → Finset (Fin m)
  pairs : Fin k → Fin n × Fin n

/-- The polynomial `F` of Theorem 4.1 over `ℤ`, in one variable `X e` per edge:
`F = ∑_{(P₁,…,P_k)} ∏ᵢ ∏_{e ∈ E(Pᵢ)} X e`, the sum over all tuples of pairwise vertex-disjoint paths
with `Pᵢ` an `sᵢ`–`tᵢ` path in `Hᵢ`. Its value at `x : Fin m → R` in a commutative ring `R` is
`MvPolynomial.eval₂ (Int.castRingHom R) x F`. -/
noncomputable def enumPoly (G : Digraph n m) (H : Fin k → Finset (Fin m))
    (pairs : Fin k → Fin n × Fin n) : MvPolynomial (Fin m) ℤ := by
  classical
  exact ∑ P ∈ (Fintype.piFinset fun _ : Fin k => listsUpTo (Fin m) n).filter
      (G.IsSolutionIn H pairs), ∏ i, ((P i).map X).prod

/-- Proof of Theorem 4.7 (p.22), "keep one lightest copy of every set of parallel edges": the edges
`e` such that every edge `e'` with the same tail and head is heavier, or equally heavy with a larger
index. Exactly one edge per ordered vertex pair that carries an edge is kept. -/
noncomputable def lightestCopies (G : Digraph n m) (wt : Fin m → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun e => ∀ e', G.tail e' = G.tail e → G.head e' = G.head e →
    wt e < wt e' ∨ (wt e = wt e' ∧ e ≤ e')

/-- `dist_G(s, v)` with values in `WithTop ℝ`: the least weight of an `s`–`v` path of `G`, and `⊤`
when there is none (the minimum over the finite set of paths). -/
noncomputable def dist (G : Digraph n m) (wt : Fin m → ℝ) (s v : Fin n) : WithTop ℝ :=
  (pathsOf G.tail G.head (· ∈ (Finset.univ : Finset (Fin m))) s v).inf
    fun p => ((pathWeight wt p : ℝ) : WithTop ℝ)

/-- Proof of Theorem 4.7 (p.22): the tight graph of the source `s`, "the edges (u, v) with
d(u) < +∞ and d(v) = d(u) + w(u, v)", where `d = dist_G(s, ·)`. -/
noncomputable def tightEdges (G : Digraph n m) (wt : Fin m → ℝ) (s : Fin n) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun e => dist G wt s (G.tail e) ≠ ⊤ ∧
    dist G wt s (G.head e) = dist G wt s (G.tail e) + ((wt e : ℝ) : WithTop ℝ)

end DisjointPathsDAG


