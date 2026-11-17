-- Prove2me | Definitions.Def_PredAdvice_Supplement_IsExactHopset
-- name    : PredAdvice_Supplement_IsExactHopset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:29:22.363469+00:00
-- url     : https://prove2.me/theorems/16eeb7b5-8a8f-4960-9696-0a8b262766e2
-- title:
--   Exact $D$-hopsets and edge-centered three-hopsets, directed and undirected
-- statement:
--   Let $G$ be a finite unweighted graph on a vertex set $V$ with distance $\mathrm{dist}_G(x,y)\in\mathbb N\cup\{+\infty\}$. A **hop** $(x,y)$ is an additional edge of weight $\mathrm{dist}_G(x,y)$ (a *metric hop*). For a finite set $H$ of hops, a route $u=w_0,w_1,\dots,w_r=v$ in $G\cup H$ is a sequence in which every step either stays at the same vertex, follows an edge of $G$, or follows a hop of $H$; its weight is
--
--   $$\sum_{i=1}^{r}\mathrm{dist}_G(w_{i-1},w_i).$$
--
--   $H$ is an **exact $D$-hopset** if every pair $(u,v)$ with $\mathrm{dist}_G(u,v)<\infty$ has a route in $G\cup H$ with $r\le D$ steps and weight exactly $\mathrm{dist}_G(u,v)$. Its **size** is the number of hops $(x,y)\in H$ with $x\neq y$; diagonal edges are free.
--
--   $H$ is an **edge-centered three-hopset** if it is an exact three-hopset and, for every reachable pair $(u,v)$, there are vertices $x,y$ such that $(u,x)$ is an edge of $G$, a hop of $H$, or $x=u$; $(x,y)$ is an edge of $G$ or $x=y$; $(y,v)$ is an edge of $G$, a hop of $H$, or $y=v$; and
--
--   $$\mathrm{dist}_G(u,x)+\mathbf 1_{x\neq y}+\mathrm{dist}_G(y,v)=\mathrm{dist}_G(u,v).$$
--
--   For a directed graph the hops are ordered pairs, traversed in their direction. For an undirected graph the hops are unordered pairs, traversed in either direction, and distances are those of the symmetric digraph with the same adjacency.
--
--   These are the objects bounded by Theorems 1.2, 1.3, 1.5, 1.7 and 3.1.
--
--   **Formalization Note** Distances are the base mission's `PredAdvice.dist`. A hop between an unreachable pair is allowed in a hop set, but its weight is $+\infty$, so it lies on no exact route and only adds to the size.
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), exact D-hopsets, §1.1, p.4 and footnote 4; edge-centered three-hopsets, §1.2, p.5; metric hops and diagonal edges, §2, p.10

import Mathlib
import Definitions.Def_PredAdvice_dist

set_option autoImplicit false

namespace PredAdvice

namespace Supplement

/-!
# Exact hopsets and edge-centered three-hopsets, directed and undirected

Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027
submission (manuscript sha256 0ae8a68d…): exact `D`-hopsets, §1.1, p.4 (with footnote 4);
edge-centered three-hopsets, §1.2, p.5; metric hops and diagonal edges, §2, p.10.

**Formalization Note.**
* Distances are the base mission's `PredAdvice.dist` (in `ℕ∞`, `⊤` for unreachable pairs).
* A hop `(x, y)` carries weight `dist_G(x, y)` ("metric hops", p.10); every step of a route is
  weighted by the `G`-distance between its endpoints, so an edge of `G` between distinct vertices
  weighs `1`.
* A route may stay at a vertex ("implicit identity edge (x, x) of weight zero", p.10; "any hop with
  the same endpoints is allowed to be omitted", p.5).
* The size of a hopset counts only its off-diagonal pairs ("do not count such edges toward the
  hopset size", p.10). Hops are not required to join reachable pairs: an unreachable hop has weight
  `⊤` and can never lie on an exact route, and it only adds to the size.
* An undirected graph is a `SimpleGraph`; its distances are those of the symmetric digraph with the
  same adjacency (`toDigraph`), and its hops are unordered pairs (`Sym2`), usable in both
  directions (footnote 4, p.4).
-/

/-- The weight of a route `[w₀, …, w_r]`: `∑ᵢ dist_G(w_{i−1}, w_i)` (each hop and each edge
weighted by the distance between its endpoints, p.10). -/
noncomputable def routeWeight {V : Type*} (G : Digraph V) (p : List V) : ℕ∞ :=
  ((p.zip p.tail).map fun e => dist G e.1 e.2).sum

/-- One step of a route in `G ∪ H` for a directed graph `G` and a set of directed hops `H`: stay
at the vertex, follow an edge of `G`, or follow a hop of `H`. -/
def IsStep {V : Type*} (G : Digraph V) (H : Finset (V × V)) (a b : V) : Prop :=
  a = b ∨ G.Adj a b ∨ (a, b) ∈ H

/-- An **exact realization** of `(u, v)` with at most `D` hops in `G ∪ H` (p.4): a vertex list
`u = w₀, w₁, …, w_r = v` with `r ≤ D` steps of `G ∪ H` whose total weight is `dist_G(u, v)`. -/
def IsRealization {V : Type*} (G : Digraph V) (H : Finset (V × V)) (D : ℕ) (u v : V)
    (p : List V) : Prop :=
  p.head? = some u ∧ p.getLast? = some v ∧ p.IsChain (IsStep G H) ∧ p.length ≤ D + 1 ∧
    routeWeight G p = dist G u v

/-- An **exact `D`-hopset** for the directed graph `G` (§1.1, p.4): "a set H of additional
edges, each (x, y) ∈ H of weight dist_G(x, y), such that every finite distance in G is realized
in G ∪ H by a path of at most D edges." -/
def IsExactHopset {V : Type*} (G : Digraph V) (D : ℕ) (H : Finset (V × V)) : Prop :=
  ∀ u v : V, Reachable G u v → ∃ p : List V, IsRealization G H D u v p

/-- The size of a directed hopset: its number of off-diagonal pairs (diagonal edges are free,
p.10). -/
def hopsetSize {V : Type*} [DecidableEq V] (H : Finset (V × V)) : ℕ :=
  (H.filter fun e => e.1 ≠ e.2).card

/-- An **edge-centered three-hopset** for the directed graph `G` (§1.2, p.5): an exact
three-hopset `H` such that for every reachable pair `(u, v)` there are `x, y` with `(u, x)` and
`(y, v)` hops of `G ∪ H` (or omitted: `x = u`, `y = v`), `(x, y)` an edge of `G` or `x = y`, and
`dist(u, x) + 1_{x≠y} + dist(y, v) = dist(u, v)`. -/
def IsEdgeCentered3Hopset {V : Type*} [DecidableEq V] (G : Digraph V) (H : Finset (V × V)) : Prop :=
  IsExactHopset G 3 H ∧
    ∀ u v : V, Reachable G u v → ∃ x y : V,
      (x = u ∨ G.Adj u x ∨ (u, x) ∈ H) ∧ (x = y ∨ G.Adj x y) ∧
      (y = v ∨ G.Adj y v ∨ (y, v) ∈ H) ∧
      dist G u x + (if x = y then 0 else 1) + dist G y v = dist G u v

/-- The symmetric digraph of a simple graph: the same adjacency, each undirected edge read as two
opposite directed edges (footnote 4, p.4). Distances of an undirected graph `G` are
`dist (toDigraph G)`. -/
def toDigraph {V : Type*} (G : SimpleGraph V) : Digraph V where
  Adj := G.Adj

/-- One step of a route in `G ∪ H` for an undirected graph `G` and a set of unordered hops `H`. -/
def IsStepU {V : Type*} (G : SimpleGraph V) (H : Finset (Sym2 V)) (a b : V) : Prop :=
  a = b ∨ G.Adj a b ∨ s(a, b) ∈ H

/-- An exact realization of `(u, v)` with at most `D` hops in `G ∪ H`, undirected case. -/
def IsRealizationU {V : Type*} (G : SimpleGraph V) (H : Finset (Sym2 V)) (D : ℕ) (u v : V)
    (p : List V) : Prop :=
  p.head? = some u ∧ p.getLast? = some v ∧ p.IsChain (IsStepU G H) ∧ p.length ≤ D + 1 ∧
    routeWeight (toDigraph G) p = dist (toDigraph G) u v

/-- An **exact `D`-hopset** for the undirected graph `G` (§1.1, p.4, footnote 4): unordered hops
of weight `dist_G`, every finite distance realized in `G ∪ H` by at most `D` hops. -/
def IsExactHopsetU {V : Type*} (G : SimpleGraph V) (D : ℕ) (H : Finset (Sym2 V)) : Prop :=
  ∀ u v : V, Reachable (toDigraph G) u v → ∃ p : List V, IsRealizationU G H D u v p

/-- The size of an undirected hopset: its number of non-diagonal unordered pairs. -/
def hopsetSizeU {V : Type*} [DecidableEq V] (H : Finset (Sym2 V)) : ℕ :=
  (H.filter fun e => ¬ e.IsDiag).card

/-- An **edge-centered three-hopset** for the undirected graph `G` (§1.2, p.5). -/
def IsEdgeCentered3HopsetU {V : Type*} [DecidableEq V] (G : SimpleGraph V) (H : Finset (Sym2 V)) : Prop :=
  IsExactHopsetU G 3 H ∧
    ∀ u v : V, Reachable (toDigraph G) u v → ∃ x y : V,
      (x = u ∨ G.Adj u x ∨ s(u, x) ∈ H) ∧ (x = y ∨ G.Adj x y) ∧
      (y = v ∨ G.Adj y v ∨ s(y, v) ∈ H) ∧
      dist (toDigraph G) u x + (if x = y then 0 else 1) + dist (toDigraph G) y v =
        dist (toDigraph G) u v

end Supplement

end PredAdvice


