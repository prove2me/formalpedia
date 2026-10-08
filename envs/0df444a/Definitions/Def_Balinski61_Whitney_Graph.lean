-- Prove2me | Definitions.Def_Balinski61_Whitney_Graph
-- name    : Balinski61_Whitney_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:43:39.639987+00:00
-- url     : https://prove2.me/theorems/11743bae-9585-42de-ac68-4ee746755f49
-- title:
--   n-tuply connected graphs and n disjoint paths (p. 431)
-- statement:
--   Balinski (p. 431) works with a **graph** $G(\pi, \Delta)$: a finite collection of points $\pi$ together with a collection $\Delta$ of lines, each line being a pair of distinct points. A **path** is a sequence of lines $(p_1,p_2),(p_2,p_3),\dots,(p_k,p_{k+1})$ with $k \ge 1$ and consecutive points distinct, and paths are **disjoint** if they have no points in common except possibly their first and last points.
--
--   This definition introduces two notions for a finite simple graph $G$ on a vertex set $V$.
--
--   1. $G$ is **$n$-tuply connected** if it has at least $n+1$ points and it is impossible to disconnect it by dropping out $n-1$ or fewer points:
--   $$
--   |V| \ge n+1 \quad\text{and}\quad G - X \text{ is connected for every } X \subseteq V \text{ with } |X| < n .
--   $$
--   2. For points $p_s, p_k$, **$G$ has $n$ disjoint paths from $p_s$ to $p_k$** if there are $n$ pairwise distinct paths $P_1,\dots,P_n$ from $p_s$ to $p_k$, each visiting no point twice, such that any point lying on two different paths $P_i, P_j$ is $p_s$ or $p_k$.
--
--   These are the two sides of Whitney's theorem: vertex connectivity measured by deletions, and by families of internally disjoint paths.
--
--   **Formalization Note** A graph is a Mathlib `SimpleGraph` on a `Fintype` (no loops, no parallel lines, as on the page). "Dropping out $n-1$ or fewer points" is written as $|X| < n$ to avoid truncated subtraction in $\mathbb N$; $G - X$ is the subgraph induced on the complement of $X$, and Mathlib's `Connected` means nonempty and any two points joined. At $n = 0$ the notion says $|V| \ge 1$; at $n = 1$ it says $G$ is connected with at least two points. The paths are required to be pairwise distinct and simple (`IsPath`). The paper's path syntax permits repeated points, but its theorem requires the conventional simple-path reading: in a graph with lines $p_s a$, $p_s b$, and $p_s p_k$, the distinct walks $p_s,a,p_s,p_k$ and $p_s,b,p_s,p_k$ share only their endpoints, while the graph is not $2$-tuply connected. Injectivity separately prevents repeated copies of the direct line from counting. Mission I of this series defines the same connectivity notion over `Set.encard`; the duplication is deliberate (draft definitions cannot import each other).
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 431, Section 2: definitions of graph, path, disjoint paths, n-tuply connected

import Mathlib

namespace Balinski61.Whitney

/-- A graph is **`n`-tuply connected** (Balinski, p. 431) if it has at least `n + 1` points and it
is impossible to disconnect it by dropping out `n − 1` or fewer points: for every set `X` of fewer
than `n` points, the graph induced on the remaining points is connected. -/
def IsNTuplyConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ) : Prop :=
  n + 1 ≤ Fintype.card V ∧
    ∀ X : Finset V, X.card < n → (G.induce ((↑X : Set V)ᶜ)).Connected

/-- `HasNDisjointPaths G n ps pk` (p. 431): there are `n` distinct paths from `ps` to `pk` in `G`
that are pairwise disjoint, i.e. no two of them have a point in common other than their first
point `ps` and their last point `pk`. -/
def HasNDisjointPaths {V : Type*} (G : SimpleGraph V) (n : ℕ) (ps pk : V) : Prop :=
  ∃ P : Fin n → G.Walk ps pk, Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
    ∀ i j, i ≠ j → ∀ x, x ∈ (P i).support → x ∈ (P j).support → x = ps ∨ x = pk

end Balinski61.Whitney


