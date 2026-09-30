-- Prove2me | Definitions.Def_HeldKarp_Ascent_IsOneTree
-- name    : HeldKarp_Ascent_IsOneTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T05:54:42.086552+00:00
-- url     : https://prove2.me/theorems/cfef48d0-7175-4b0e-a083-de91bcf34453
-- title:
--   1-trees and tours on the complete graph $K_n$
-- statement:
--   Let $K_n$ be the complete undirected graph on the vertex set $\{1, 2, \dots, n\}$, and view every subgraph of $K_n$ as a simple graph on these $n$ vertices.
--
--   1. A **1-tree** is a graph $G$ such that the subgraph of $G$ induced on $\{2, 3, \dots, n\}$ is a tree (connected and without cycles), and vertex $1$ is incident with exactly two distinct edges of $G$.
--   2. A **tour** is a cycle passing through each vertex exactly once; equivalently, a connected graph in which every vertex has degree $2$:
--   $$\text{$G$ is a tour} \iff G \text{ connected and } \deg_G(i) = 2 \ \text{ for all } i.$$
--
--   Every edge of a 1-tree either joins two vertices of $\{2,\dots,n\}$, and then belongs to the spanning tree on these vertices, or is one of the two edges at vertex $1$. A 1-tree has exactly $n$ edges, and its unique cycle passes through vertex $1$. A tour is a 1-tree in which every vertex has degree $2$. These are the combinatorial objects over which Held and Karp's lower bound $w(\pi)$ is a minimum.
--
--   **Formalization Note** Vertices are `Fin n`, and the paper's vertex $1$ is `0 : Fin n`. "Two distinct edges at vertex 1" is `G.degree 0 = 2` (a simple graph has neither loops nor repeated edges). The tour predicate is the degree form of the paper's observation (i); for $n \ge 3$ it describes exactly the Hamiltonian cycles of $K_n$. For $n \le 2$ neither predicate is satisfiable. The 1-tree predicate has the same body as `SupplyChainTheory.Is1Tree` with root `0`.
-- source:
--   Held & Karp, The traveling-salesman problem and minimum spanning trees: Part II, Math. Programming 1 (1971), DOI 10.1007/BF01584070, p. 7 (PDF p. 2), §1: definitions of tour and 1-tree, observation (i)

import Mathlib

open Classical

namespace HeldKarp.Ascent

/-- **1-tree** (Held & Karp, *The traveling-salesman problem and minimum spanning trees: Part II*,
Math. Programming 1 (1971), §1, p. 7 (PDF p. 2)): "A 1-tree is a tree having vertex set
{2, 3, ..., n}, together with two distinct edges at vertex 1."

A simple graph `G` on the vertices of the complete graph `K_n` is a 1-tree when the subgraph
induced on the vertices other than the special vertex is a tree, and the special vertex has
exactly two neighbours.

Formalization Note: the paper's vertices `1, …, n` are `Fin n`, and the paper's special vertex 1
is `0 : Fin n` (hence `[NeZero n]`). A subgraph of `K_n` is a `SimpleGraph (Fin n)`. A simple graph
has no loops and no repeated edges, so "two distinct edges at vertex 1" is `G.degree 0 = 2`, and
every edge of `G` either avoids `0` (and then lies in the induced tree) or is one of these two
edges. The body is the same as `SupplyChainTheory.Is1Tree` (published definition
`SupplyChainTheory_tsp`) with root `0`. For `n ≤ 2` no graph is a 1-tree. -/
def IsOneTree {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) : Prop :=
  (G.induce {v : Fin n | v ≠ 0}).IsTree ∧ G.degree 0 = 2

/-- **Tour** (Held & Karp 1971, §1, p. 7 (PDF p. 2)): "A tour is a cycle passing through each
vertex exactly once."

Formalization Note: a tour is encoded, as in the paper's observation (i) on p. 7 ("a tour is simply
a 1-tree in which each vertex has degree 2"), as a connected simple graph on `Fin n` in which every
vertex has degree 2. For `n ≥ 3` these are exactly the edge sets of the Hamiltonian cycles of
`K_n`; for `n ≤ 2` no graph qualifies. -/
def IsTour {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.Connected ∧ ∀ v : Fin n, G.degree v = 2

end HeldKarp.Ascent


