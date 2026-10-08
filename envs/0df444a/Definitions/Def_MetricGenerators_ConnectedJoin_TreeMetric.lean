-- Prove2me | Definitions.Def_MetricGenerators_ConnectedJoin_TreeMetric
-- name    : MetricGenerators_ConnectedJoin_TreeMetric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:30.666287+00:00
-- url     : https://prove2.me/theorems/2cd55e56-6b52-40a1-a813-8f4e2368162a
-- title:
--   Tree metrics and their realizations (§3.2, p. 391); inclusionwise minimal realizations; a tree that is an S-join
-- statement:
--   Let $X$ be a set and $\mu:X\times X\to\mathbb N$. Following Sebő and Tannier, a **realization** of $(X,\mu)$ is a tree $A$ (a finite connected acyclic graph with unit edge lengths) together with an **isometry** $g$ from $(X,\mu)$ to $A$, that is, a map $g:X\to V(A)$ with
--
--   $$d_A\bigl(g(x),g(y)\bigr)=\mu(x,y)\qquad\text{for all }x,y\in X,$$
--
--   where $d_A$ is the distance in $A$. The function $\mu$ is a **tree metric** if it is a metric (in particular $\mu(x,y)=0$ only for $x=y$) that has a realization.
--
--   A realization $(A,g)$ is **inclusionwise minimal** if no proper subtree of $A$ contains $g(X)$: every connected subgraph of $A$ containing all the points $g(x)$ contains every vertex of $A$.
--
--   Finally, for a graph $A$ and a vertex set $S$, $A$ is an **$S$-join** if its own edge set is an $S$-join of $A$: a vertex of $A$ has odd degree exactly when it lies in $S$. Theorem 6 of the paper asks this of the minimal realization of $\mu_G|_T$ with $S=g(T)$.
--
--   The minimal realization of a tree metric is unique up to an isomorphism respecting the points of $X$; this makes "the" minimal realization in Theorem 6 well defined.
--
--   **Formalization Note.** A realization is a simple graph on $\mathrm{Fin}\,N$ for some $N\in\mathbb N$ that is a tree, plus a map $g:X\to\mathrm{Fin}\,N$; restricting the vertex type to $\mathrm{Fin}\,N$ avoids quantifying over a universe, and the minimal realizations are finite. The metric axioms other than "$\mu(x,y)=0\Rightarrow x=y$" follow from the realization identity, so only that clause is written. A connected subgraph of a tree containing all its vertices is the whole tree, which is why minimality is stated on vertex sets. The degree in "$S$-join" is the degree in $A$.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 391, §3.2 (tree metric, realization, inclusionwise minimal realization); p. 385, §2 (isometry); p. 392, Theorem 6 (the tree A is a T′-join)

import Mathlib

namespace MetricGenerators.ConnectedJoin

/-- A realization of `μ` (Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res.
29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, §3.2, p. 391): "A metric μ on a set X is said
to be a tree metric if there exists a tree A, and an isometry from (X, μ) to A. The tree A will be
called a realization of (X, μ)." Here `A` is a tree and `g : X → V(A)` is an isometry: the
distance in `A` between `g x` and `g y` is `μ x y` (isometry as defined on p. 385).

**Formalization Note.** The tree is a simple graph on `Fin N` for some `N : ℕ`, with unit edge
lengths (the metrics of the paper are graph distances, values in `ℕ`). Taking the vertex type to be
`Fin N` rather than an arbitrary type avoids quantifying over a universe; the realizations used in
the paper (the minimal ones) are finite trees. -/
def IsRealization {X : Type*} (μ : X → X → ℕ) {N : ℕ} (A : SimpleGraph (Fin N))
    (g : X → Fin N) : Prop :=
  A.IsTree ∧ ∀ x y : X, A.dist (g x) (g y) = μ x y

/-- A tree metric (Sebő and Tannier 2004, §3.2, p. 391): a metric `μ` on `X` that has a
realization.

**Formalization Note.** `μ` is an `ℕ`-valued function; the clause `μ x y = 0 → x = y` is the part
of "μ is a metric" not implied by the existence of a realization (symmetry, the triangle
inequality and `μ x x = 0` follow from the realization identity). -/
def IsTreeMetric {X : Type*} (μ : X → X → ℕ) : Prop :=
  (∀ x y : X, μ x y = 0 → x = y) ∧
    ∃ (N : ℕ) (A : SimpleGraph (Fin N)) (g : X → Fin N), IsRealization μ A g

/-- An inclusionwise minimal realization (Sebő and Tannier 2004, §3.2, p. 391: "a unique (up to
isomorphism) inclusionwise minimal tree A which is a realization of μ"): a realization `(A, g)`
such that no proper subtree of `A` contains `g(X)`.

**Formalization Note.** "Subtree" is a connected subgraph `A'` of `A`; any such subgraph that
contains `g(X)` is again a realization (in a tree, distances inside a connected subgraph equal
distances in the tree), so the condition says exactly that no realization is properly contained in
`A`. A connected subgraph of a tree containing every vertex is the whole tree, so the condition is
stated on vertex sets. -/
def IsMinimalRealization {X : Type*} (μ : X → X → ℕ) {N : ℕ} (A : SimpleGraph (Fin N))
    (g : X → Fin N) : Prop :=
  IsRealization μ A g ∧
    ∀ A' : A.Subgraph, A'.Connected → (∀ x : X, g x ∈ A'.verts) → A'.verts = Set.univ

open Classical in
/-- The graph `A` is an `S`-join (Sebő and Tannier 2004, Theorem 6, p. 392: "The tree A is a
T′-join"): the edge set of `A` is an `S`-join of `A`, i.e. every vertex of `A` has odd degree
exactly when it lies in `S` (the definition of a T-join, p. 389, applied to `E(A)`).

**Formalization Note.** The degree of `a` in the edge set `E(A)` is `A.degree a`. -/
def GraphIsJoin {W : Type*} [Fintype W] (A : SimpleGraph W) (S : Set W) : Prop :=
  ∀ a : W, Odd (A.degree a) ↔ a ∈ S

end MetricGenerators.ConnectedJoin


