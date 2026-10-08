-- Prove2me | Definitions.Def_Balinski61_Connectivity_TuplyConnected
-- name    : Balinski61_Connectivity_TuplyConnected
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:27:50.173145+00:00
-- url     : https://prove2.me/theorems/ef968cee-4917-4e1d-9e27-c50afb549636
-- title:
--   $n$-tuply connected graphs and $n$ disjoint paths between two points
-- statement:
--   Let $G$ be a graph (a set of points together with lines joining pairs of distinct points). A **path** is a sequence of lines $(p_1,p_2),(p_2,p_3),\dots,(p_k,p_{k+1})$ with consecutive points distinct, and $G$ is **connected** if there is a path between any two of its points (Balinski, p. 431).
--
--   1. **$n$-tuply connected.** Balinski defines (p. 431): "an $n$-tuply connected graph $G$ to be a graph with at least $n+1$ points and such that it is impossible to disconnect it by dropping out $n-1$ or fewer points." That is, $G$ is $n$-tuply connected if
--   $$|V(G)|\ge n+1\quad\text{and}\quad G-X \text{ is connected for every set } X \text{ of at most } n-1 \text{ points},$$
--   where $G-X$ is the graph induced on the points not in $X$.
--   2. **$n$ disjoint paths.** "Paths are said to be disjoint if they have no points except possibly first and last points in common" (p. 431). Two points $u,v$ are joined by $n$ disjoint paths if there are $n$ distinct paths $P_1,\dots,P_n$ from $u$ to $v$, each visiting no point twice, such that any point lying on two different paths $P_i,P_j$ is $u$ or $v$.
--
--   Today the first notion is called vertex $n$-connectivity; the second is the conclusion of Menger's and Whitney's theorems. They are the graph-theoretic vocabulary of Balinski's THEOREM and COROLLARY.
--
--   **Formalization Note** For `G : SimpleGraph V`, `IsNTuplyConnected G n` says that `Set.univ` has extended cardinality `encard` at least $n+1$ and that `G.induce Xᶜ` is connected for every `X` with `X.encard < n`; "$n-1$ or fewer" is written `X.encard < n` to avoid natural-number subtraction, and `encard` avoids the junk value $0$ of `Nat.card` on infinite types. Mathlib's `Connected` includes nonemptiness. A path of the paper is a Mathlib `Walk` (consecutive points of a simple graph are distinct); in `HasDisjointPaths` the $n$ walks are required to be paths (`IsPath`, no repeated point) and to be pairwise distinct (`Function.Injective`), since otherwise $n$ copies of a single line $uv$ would be pairwise "disjoint". The same notions are defined independently, as drafts, in the companion mission on Whitney's theorem.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 431, Section 2 (definitions of path, disjoint paths, connected, n-tuply connected graph)

import Mathlib

namespace Balinski61.Connectivity

/-- A graph is **`n`-tuply connected** (p. 431) if it has at least `n + 1` points and it cannot
be disconnected by dropping out `n − 1` or fewer points: for every set `X` of fewer than `n`
points, the graph induced on the remaining points is connected. -/
def IsNTuplyConnected {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ((n : ℕ∞) + 1 ≤ (Set.univ : Set V).encard) ∧
    ∀ X : Set V, X.encard < n → (G.induce Xᶜ).Connected

/-- `HasDisjointPaths G u v n` (p. 431): there are `n` distinct paths from `u` to `v` in `G`
that are pairwise disjoint, i.e. no two of them have a point in common other than their first
point `u` and last point `v`. -/
def HasDisjointPaths {V : Type*} (G : SimpleGraph V) (u v : V) (n : ℕ) : Prop :=
  ∃ P : Fin n → G.Walk u v, Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
    ∀ i j, i ≠ j → ∀ x, x ∈ (P i).support → x ∈ (P j).support → x = u ∨ x = v

end Balinski61.Connectivity


