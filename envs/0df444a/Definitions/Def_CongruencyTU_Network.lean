-- Prove2me | Definitions.Def_CongruencyTU_Network
-- name    : CongruencyTU_Network
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:02.005977+00:00
-- url     : https://prove2.me/theorems/9af5e9ed-c25d-40a8-b2c4-264612bdea05
-- title:
--   Network matrices
-- statement:
--   A matrix $T$ is a **network matrix** if its rows can be indexed by the arcs of a directed spanning tree $(V,U)$ and its columns by the arcs of a directed graph $(V,A)$ on the same vertex set (parallel arcs allowed) such that, for every arc $a=(v,w)\in A$ and every arc $u\in U$,
--   $$
--   T_{u,a}=\begin{cases}1&\text{if the unique $v$–$w$ path in $U$ passes through $u$ forwardly},\\0&\text{if it does not pass through $u$},\\-1&\text{if it passes through $u$ backwardly.}\end{cases}
--   $$
--   A directed graph is a spanning tree if it is one when directions are ignored.
--
--   **Formalization Note** For $k$ rows the vertex set is $\{0,\dots,k\}$ (a spanning tree has $|V|-1$ arcs). The tree arcs are loop-free, pairwise non-parallel, and their undirected graph is a tree in Mathlib's sense. Columns are arbitrary ordered pairs of vertices (loops give zero columns).
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, Definition 31, p.23 (PDF p.24)

import Mathlib

open Classical

namespace CongruencyTU

/-! # Network matrices

Nägele–Santiago–Zenklusen, arXiv:2109.03148v3 (preprint), Definition 31, p.23 (PDF p.24):
"A matrix `T` is a network matrix if the rows of `T` can be indexed by the edges of a directed
spanning tree `(V, U)`, and the columns can be indexed by the edges of a directed graph `(V, A)` on
the same vertex set, such that for every arc `a = (v, w) ∈ A` and every arc `u ∈ U`, `T_{u,a}` is
`1` if the unique `v`–`w` path in `U` passes through `u` forwardly, `0` if it does not pass through
`u`, and `−1` if it passes through `u` backwardly." A directed graph is a spanning tree if it is one
when edge directions are ignored; `(V, A)` may have parallel arcs.

**Formalization Note.** A spanning tree on `V` has `|V| − 1` arcs, so for a matrix with `k` rows the
vertex set is `Fin (k + 1)`. Arc `u` of the tree is the ordered pair `tree u = (tail, head)`; the
tree's arcs are loop-free and pairwise non-parallel (they are the edges of a tree), and their
undirected graph `treeGraph tree` is a tree in Mathlib's sense (connected and acyclic). Column `a`
is the arc `arc a = (v, w)`; arcs may repeat (parallel arcs) and may be loops (a loop gives a zero
column, its `v`–`v` path being empty). "Passes through `u` forwardly" means the path contains the
dart `(tail u, head u)`; backwardly, the dart `(head u, tail u)`. In a tree the `v`–`w` path is
unique, so "some path" and "the path" agree. -/

/-- The undirected graph of the tree arcs. -/
def treeGraph {k : ℕ} (tree : Fin k → Fin (k + 1) × Fin (k + 1)) : SimpleGraph (Fin (k + 1)) :=
  SimpleGraph.fromEdgeSet (Set.range fun u => s((tree u).1, (tree u).2))

/-- `1` if the `v`–`w` path of `G` traverses the arc `u = (tail, head)` forwardly, `−1` if it
traverses it backwardly, `0` otherwise. -/
noncomputable def pathSign {V : Type} (G : SimpleGraph V) (u : V × V) (v w : V) : ℤ :=
  if ∃ p : G.Walk v w, p.IsPath ∧ u ∈ p.darts.map (·.toProd) then 1
  else if ∃ p : G.Walk v w, p.IsPath ∧ (u.2, u.1) ∈ p.darts.map (·.toProd) then -1
  else 0

/-- **Network matrix** (Definition 31). -/
def IsNetworkMatrix {k n : ℕ} (T : Matrix (Fin k) (Fin n) ℤ) : Prop :=
  ∃ (tree : Fin k → Fin (k + 1) × Fin (k + 1)) (arc : Fin n → Fin (k + 1) × Fin (k + 1)),
    (treeGraph tree).IsTree ∧ (∀ u, (tree u).1 ≠ (tree u).2) ∧
    Function.Injective (fun u => s((tree u).1, (tree u).2)) ∧
    ∀ u a, T u a = pathSign (treeGraph tree) (tree u) (arc a).1 (arc a).2

end CongruencyTU


