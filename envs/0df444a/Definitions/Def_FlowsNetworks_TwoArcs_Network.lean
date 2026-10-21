-- Prove2me | Definitions.Def_FlowsNetworks_TwoArcs_Network
-- name    : FlowsNetworks_TwoArcs_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:27.87991+00:00
-- url     : https://prove2.me/theorems/0ce94a05-cbb1-4a2e-aea0-6b4254bfffd3
-- title:
--   Network $[N;\mathcal A]$ with sources $S$ and sinks $T$: flows (7.1)–(7.3), the maximal flow value $\bar v$, cuts separating $S$ and $T$
-- statement:
--   A **directed network** $[N;\mathcal A]$ consists of a finite set $N$ of nodes and a set $\mathcal A$ of ordered pairs $(x,y)$ of nodes, the **arcs**; an arc $(x,y)$ has **initial node** $x$ and **terminal node** $y$, there are no loops ($x\neq y$), and there is at most one arc from $x$ to $y$, although $(x,y)$ and $(y,x)$ may both be arcs. The nodes carry a set $S$ of **sources** and a set $T$ of **sinks**, disjoint from each other; the remaining nodes $R = N\setminus(S\cup T)$ are **intermediate**.
--
--   For a capacity function $c$ on the arcs with values in $[0,\infty]$, a **flow from $S$ to $T$** is a real-valued function $f$ on the arcs (extended by $0$ off the arcs) such that
--
--   $$f(x,N) - f(N,x) = 0 \quad (x\in R), \qquad 0 \le f(x,y) \le c(x,y) \quad ((x,y)\in\mathcal A),$$
--
--   where $f(x,N)=\sum_y f(x,y)$ and $f(N,x)=\sum_y f(y,x)$. Its **value** is $v = f(S,N) - f(N,S) = \sum_{x\in S}\bigl(f(x,N)-f(N,x)\bigr)$. The **maximal flow value** $\bar v\in[0,\infty]$ is the supremum of the values of all flows (the zero flow has value $0$); it is the value of a maximal flow, and it equals $\infty$ exactly when flow values are unbounded, which can happen only when some capacities are infinite.
--
--   A node set $X$ with $S\subseteq X$ and $T\cap X=\emptyset$ determines the **cut** $(X,\bar X)$ **separating $S$ and $T$**: the set of arcs $(x,y)$ with $x\in X$, $y\notin X$. Its **capacity** is $c(X,\bar X) = \sum_{(x,y)\in\mathcal A,\ x\in X,\ y\notin X} c(x,y)$.
--
--   These are the objects of Ford and Fulkerson's Chapter I (§1 for networks, §7 for several sources and sinks), on which every statement of the mission is built.
--
--   **Formalization Note** Nodes form a `Fintype` with decidable equality; arcs are a `Finset (N × N)` with a no-loop field; capacities are functions `N × N → ℝ≥0∞`, so an infinite capacity is `⊤` and imposes no upper bound; flows are functions `N × N → ℝ` required to vanish off the arcs. The maximal flow value is an `ℝ≥0∞`-valued supremum, which is never a junk value: the set of flows is nonempty and an unbounded set of values gives `⊤`. Negative flow values (possible in principle under (7.1)–(7.3)) are clamped to $0$ by `ENNReal.ofReal`, which does not change the supremum because the zero flow has value $0$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, pp. 3–4 (§1) and pp. 28–29 (§7, (7.1)–(7.3))

import Mathlib

namespace FlowsNetworks.TwoArcs

open scoped ENNReal NNReal

/-- A directed network `[N; 𝒜]` with sources `S` and sinks `T` (Ford–Fulkerson, *Flows in
Networks*, Ch. I, §1, pp. 3–4, and §7, p. 28). The node set is the finite type `N`; `arcs` is
the set `𝒜` of ordered pairs `(x, y)`, with no loops (`x ≠ y`) and, being a set of pairs, at
most one arc from `x` to `y` (both `(x, y)` and `(y, x)` may be arcs). The nodes are
partitioned into the sources `S`, the sinks `T` and the intermediate nodes `R = N ∖ (S ∪ T)`,
so `S` and `T` are disjoint. -/
structure Network (N : Type) [Fintype N] [DecidableEq N] where
  arcs : Finset (N × N)
  no_loops : ∀ a ∈ arcs, a.1 ≠ a.2
  sources : Finset N
  sinks : Finset N
  sources_sinks_disjoint : Disjoint sources sinks

variable {N : Type} [Fintype N] [DecidableEq N]

/-- `f(x, N) = Σ_y f(x, y)`, the flow out of `x`. Flows vanish off the arcs (see `IsFlow`), so
this is the sum over the arcs leaving `x`. -/
def outflow (f : N × N → ℝ) (x : N) : ℝ := ∑ y, f (x, y)

/-- `f(N, x) = Σ_y f(y, x)`, the flow into `x`. -/
def inflow (f : N × N → ℝ) (x : N) : ℝ := ∑ y, f (y, x)

/-- A flow from `S` to `T` (Ch. I, §7, p. 28) for the capacity function `c`, whose values may be
`∞` (`⊤`): `f` is real valued on the arcs and zero off them (a convention), and
* (7.1) `f(x, N) − f(N, x) = 0` for every intermediate node `x ∉ S ∪ T`;
* (7.2) `0 ≤ f(x, y) ≤ c(x, y)` for every arc `(x, y) ∈ 𝒜` (no upper bound when `c(x, y) = ∞`). -/
def IsFlow (G : Network N) (c : N × N → ℝ≥0∞) (f : N × N → ℝ) : Prop :=
  (∀ a, a ∉ G.arcs → f a = 0) ∧
  (∀ a ∈ G.arcs, 0 ≤ f a ∧ ENNReal.ofReal (f a) ≤ c a) ∧
  (∀ x, x ∉ G.sources → x ∉ G.sinks → outflow f x - inflow f x = 0)

/-- The value (7.3) of a flow from `S` to `T`: `v = f(S, N) − f(N, S)`. -/
def flowValue (G : Network N) (f : N × N → ℝ) : ℝ :=
  ∑ x ∈ G.sources, outflow f x - ∑ x ∈ G.sources, inflow f x

/-- The maximal flow value `v̄` from `S` to `T` for the capacities `c`, as an element of
`[0, ∞]`: the supremum of the values of all flows. The zero flow is a flow of value `0`, so the
supremum is that of a nonempty set; it is `∞` exactly when flow values are unbounded (possible
only when some capacities are `∞`), and it is the value of a maximal flow when one exists. -/
noncomputable def maxFlowValue (G : Network N) (c : N × N → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (f : N × N → ℝ) (_ : IsFlow G c f), ENNReal.ofReal (flowValue G f)

/-- A node set `X` determines a cut `(X, X̄)` separating `S` and `T` (Ch. I, §7, p. 29) when
`S ⊆ X` and `T ⊆ X̄`, i.e. `X` contains every source and no sink. -/
def IsSeparating (G : Network N) (X : Finset N) : Prop :=
  G.sources ⊆ X ∧ Disjoint X G.sinks

/-- The capacity `c(X, X̄)` of the cut `(X, X̄)`: the sum of `c(x, y)` over the arcs
`(x, y) ∈ 𝒜` with `x ∈ X`, `y ∉ X`. -/
noncomputable def cutCapacity (G : Network N) (c : N × N → ℝ≥0∞) (X : Finset N) : ℝ≥0∞ :=
  ∑ a ∈ G.arcs.filter (fun a => a.1 ∈ X ∧ a.2 ∉ X), c a

end FlowsNetworks.TwoArcs


