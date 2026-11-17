-- Prove2me | Definitions.Def_LocalSepDecomp_Supplement_Encoding
-- name    : LocalSepDecomp_Supplement_Encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:46:20.012576+00:00
-- url     : https://prove2.me/theorems/d2583152-5549-4e1e-918a-84379664854e
-- title:
--   Finite codes of graphs and of graph-decompositions with parts (input and output of the algorithm of Theorem 2)
-- statement:
--   Codes for the input and output of the algorithm of Theorem 2.
--
--   1. A pair $(n,E)$ with $n\in\mathbb N$ and $E$ a finite list of pairs of natural numbers codes the graph on the vertex set $\{0,\dots,n-1\}$ in which distinct $a,b$ are adjacent if and only if $(a,b)$ or $(b,a)$ is listed in $E$. Every finite simple graph on $\{0,\dots,n-1\}$ has a code.
--   2. A triple $(m,H,P)$ codes a graph-decomposition with parts: $m$ is the number of nodes $0,\dots,m-1$; $H$ lists the edges of the decomposition multigraph as end-pairs (loops and parallel edges allowed, an edge is named by its position in the list); $P$ lists for each node its part, as a list of vertices and a list of edges of $G$.
--   3. The code is **well formed** for $G$ if every end is a node, there is exactly one part per node, every listed vertex is a vertex of $G$, and every listed part edge is an edge of $G$ whose two ends are listed vertices of that part. The **decoding** of a code is the graph-decomposition with parts whose nodes are $0,\dots,m-1$, whose edges are the listed end-pairs, and whose part at node $h$ is the subgraph of $G$ given by the $h$-th listed part.
--
--   These codes make "an algorithm that receives a finite graph and outputs a graph-decomposition" a statement about computable functions between countable sets.
--
--   **Formalization Note** The vertex set of a coded graph is `Fin n`. The decoding drops edges with an end out of range and part edges that are not edges of $G$ or have an unlisted end; on well-formed codes it drops nothing.
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 2 p.7 and its proof p.57; graph-decompositions with parts p.16

import Mathlib
import Definitions.Def_LocalSepDecomp_Decompositions

set_option autoImplicit false

namespace LocalSepDecomp.Supplement

/-! # Finite codes of graphs and of graph-decompositions with parts (input and output of the
algorithm of Theorem 2)

R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 2 (p.7) and its
proof (p.57); graph-decompositions with parts as on p.16.

**Formalization Note.**
1. A finite graph is given by `(n, E)`: the vertex set `Fin n` and a list `E` of pairs of
   naturals; `a ≠ b` are adjacent iff `(a, b)` or `(b, a)` is listed. Pairs with an entry `≥ n`
   and loops are ignored. Every simple graph on `Fin n` has such a code.
2. A graph-decomposition with parts is coded as `(m, H, P)`: `m` nodes `0, …, m−1`; the edges of
   the multigraph `H` as a list of end-pairs (list position = edge name; loops and parallel edges
   allowed); and, for each node, its part as a list of vertices and a list of edges of `G`.
3. `WellFormed` says that the code is meaningful: every end is a node, there is exactly one part
   per node, every listed vertex is a vertex, and every listed part edge is an edge of `G` with
   both ends among the listed vertices of that part. `decodeDecomp` decodes a code into a
   `GraphDecomp` (`Node = Fin m`); edges with an end out of range and part edges not in `G` or
   with an unlisted end are dropped by the decoding, which on well-formed codes drops nothing. -/

open SimpleGraph

/-- The simple graph on `Fin n` coded by the list `E` of vertex pairs. -/
def graphOfCode (n : ℕ) (E : List (ℕ × ℕ)) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ ((a.val, b.val) ∈ E ∨ (b.val, a.val) ∈ E)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A code `(m, H, P)` of a graph-decomposition with parts: the number `m` of nodes, the list of
end-pairs of the edges of the decomposition multigraph, and for every node its part (vertex list,
edge list). -/
abbrev DecompCode : Type := ℕ × List (ℕ × ℕ) × List (List ℕ × List (ℕ × ℕ))

/-- The code `c` is a well-formed code of a graph-decomposition with parts of `G`. -/
def WellFormed {n : ℕ} (G : SimpleGraph (Fin n)) (c : DecompCode) : Prop :=
  (∀ e ∈ c.2.1, e.1 < c.1 ∧ e.2 < c.1) ∧ c.2.2.length = c.1 ∧
    ∀ P ∈ c.2.2, (∀ v ∈ P.1, v < n) ∧
      ∀ e ∈ P.2, e.1 ∈ P.1 ∧ e.2 ∈ P.1 ∧
        ∃ a b : Fin n, a.val = e.1 ∧ b.val = e.2 ∧ G.Adj a b

/-- The part (a subgraph of `G`) coded by a vertex list and an edge list. -/
def decodePart {n : ℕ} (G : SimpleGraph (Fin n)) (P : List ℕ × List (ℕ × ℕ)) : G.Subgraph where
  verts := {v | v.val ∈ P.1}
  Adj a b := G.Adj a b ∧ a.val ∈ P.1 ∧ b.val ∈ P.1 ∧ ((a.val, b.val) ∈ P.2 ∨ (b.val, a.val) ∈ P.2)
  adj_sub h := h.1
  edge_vert h := h.2.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.symm⟩⟩

/-- The graph-decomposition with parts of `G` decoded from `c`: nodes `Fin m`, edges the listed
end-pairs (with both ends in range), part of node `h` the `h`-th listed part. -/
def decodeDecomp {n : ℕ} (G : SimpleGraph (Fin n)) (c : DecompCode) : GraphDecomp.{0, 0} G where
  Node := Fin c.1
  Edge := {i : Fin c.2.1.length // (c.2.1.get i).1 < c.1 ∧ (c.2.1.get i).2 < c.1}
  ends e := s(⟨(c.2.1.get e.1).1, e.2.1⟩, ⟨(c.2.1.get e.1).2, e.2.2⟩)
  part h := decodePart G (c.2.2.getD h.val ([], []))

end LocalSepDecomp.Supplement


