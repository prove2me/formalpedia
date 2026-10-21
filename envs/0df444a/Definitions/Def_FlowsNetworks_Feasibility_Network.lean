-- Prove2me | Definitions.Def_FlowsNetworks_Feasibility_Network
-- name    : FlowsNetworks_Feasibility_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:36.091503+00:00
-- url     : https://prove2.me/theorems/a8063c48-26c3-4a61-a6a9-8a7cafe4598f
-- title:
--   Network $[N; \mathcal A]$ with capacities, the notation $g(X, Y)$, $f(x, N)$, $f(N, x)$, and partitions into sources, intermediate nodes and sinks
-- statement:
--   Following Chapter I (§§1–2) and Chapter II (§§1–3) of Ford and Fulkerson's *Flows in Networks*, this file sets up the objects of the supply-demand and circulation theorems.
--
--   1. A **network** $G = [N; \mathcal A]$ consists of a finite set $N$ of **nodes** and a set $\mathcal A$ of ordered pairs $(x, y)$ of nodes, the **arcs**, with $x \neq y$ for every arc. There is at most one arc from $x$ to $y$, but both $(x, y)$ and $(y, x)$ may be arcs. Every arc carries a nonnegative real **capacity** $c(x, y) \ge 0$.
--   2. For node sets $X, Y \subseteq N$ and a real function $g$ on the arcs,
--   $$g(X, Y) = \sum_{(x, y) \in \mathcal A,\ x \in X,\ y \in Y} g(x, y).$$
--   In particular $f(x, N)$ is the total of $f$ on the arcs leaving the node $x$, and $f(N, x)$ the total on the arcs entering $x$. For a node set $X$, $\bar X = N - X$ is its complement.
--   3. A function $f$ on the arcs is a real function that vanishes at every pair $(x, y) \notin \mathcal A$.
--   4. Three node sets $S$, $R$, $T$ **partition** $N$ if they are pairwise disjoint and their union is $N$; any of them may be empty. In Chapter II, $S$ is the set of **sources**, $R$ of **intermediate nodes**, and $T$ of **sinks**.
--
--   These are the objects of every statement of the mission: Gale's supply-demand theorem and its two-sided form (§§1–2), the matrix criterion of Corollary 2.3, and Hoffman's circulation theorem and its extension with node bounds (§3).
--
--   **Formalization Note** Nodes form a `Fintype` with decidable equality, arcs a `Finset (N × N)`. Capacities and flows are functions $N \to N \to \mathbb R$; the values of the capacity off $\mathcal A$ are never used, since every sum $g(X, Y)$ runs over arcs only. The predicate `SupportedOnArcs` makes a flow exactly a function on $\mathcal A$. Node-set sums such as $a(S \cap \bar X) = \sum_{x \in S \cap \bar X} a(x)$ are written out as `Finset` sums in each statement. Capacities are finite reals.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, pp. 3–4 (§1, networks; no loops, at most one arc), p. 7 (§2, capacities); Chapter II, p. 2 (§1, sources, intermediate nodes, sinks, the notation f(x, N), f(N, x)), p. 25 (§3, lower bounds)

import Mathlib

namespace FlowsNetworks.Feasibility

/-- A directed network `[N; 𝒜]` with a capacity function (Ford–Fulkerson, *Flows in Networks*,
Chapter I, §1 pp. 3–4 and §2 p. 7, used throughout Chapter II). The node set `N` is a finite
type; the arc set `𝒜` is a finite set of ordered pairs, so there is at most one arc from `x` to
`y`, while both `(x, y)` and `(y, x)` may be arcs. Arcs are loop-free (`x ≠ y`). Every arc carries
a nonnegative real capacity `c(x, y)`; values of `cap` off `𝒜` play no role in any definition
below. -/
structure Network (N : Type) [Fintype N] [DecidableEq N] where
  /-- the arc set `𝒜 ⊆ N × N` -/
  arcs : Finset (N × N)
  /-- no arc leads from a node to itself -/
  loopless : ∀ p ∈ arcs, p.1 ≠ p.2
  /-- the capacity function `c` -/
  cap : N → N → ℝ
  /-- capacities are nonnegative reals -/
  cap_nonneg : ∀ p ∈ arcs, 0 ≤ cap p.1 p.2

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The book's notation `g(X, Y) = ∑ g(x, y)`, the sum over all arcs `(x, y) ∈ 𝒜` with `x ∈ X` and
`y ∈ Y`, for a real function `g` on the arcs and node sets `X, Y ⊆ N`. -/
def arcSum (G : Network N) (g : N → N → ℝ) (X Y : Finset N) : ℝ :=
  ∑ p ∈ G.arcs.filter (fun p => p.1 ∈ X ∧ p.2 ∈ Y), g p.1 p.2

/-- `f(x, N)`: the total flow on arcs leaving the node `x`. -/
def outflow (G : Network N) (f : N → N → ℝ) (x : N) : ℝ :=
  arcSum G f {x} Finset.univ

/-- `f(N, x)`: the total flow on arcs entering the node `x`. -/
def inflow (G : Network N) (f : N → N → ℝ) (x : N) : ℝ :=
  arcSum G f Finset.univ {x}

/-- A flow is a function on the arcs only: it vanishes at every pair `(x, y) ∉ 𝒜`. -/
def SupportedOnArcs (G : Network N) (f : N → N → ℝ) : Prop :=
  ∀ x y, (x, y) ∉ G.arcs → f x y = 0

/-- `S`, `R`, `T` partition the node set: they are pairwise disjoint and cover `N` (any of them
may be empty). Used for the sources `S`, intermediate nodes `R` and sinks `T` of Chapter II, §1. -/
def IsPartition (S R T : Finset N) : Prop :=
  Disjoint S R ∧ Disjoint S T ∧ Disjoint R T ∧ S ∪ R ∪ T = Finset.univ

end FlowsNetworks.Feasibility


