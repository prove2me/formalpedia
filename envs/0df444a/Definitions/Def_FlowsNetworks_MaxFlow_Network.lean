-- Prove2me | Definitions.Def_FlowsNetworks_MaxFlow_Network
-- name    : FlowsNetworks_MaxFlow_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:27.067629+00:00
-- url     : https://prove2.me/theorems/930f5239-1eea-44b8-8a5d-ab4028ec46c0
-- title:
--   Network $[N; \mathcal A]$ with capacities, the notation $g(X, Y)$, static flows, maximal flows, cuts and minimal cuts
-- statement:
--   Following Chapter I of Ford and Fulkerson's *Flows in Networks* (§§1–4 and §9), this file sets up the objects of the max flow min cut theorem.
--
--   1. A **network** $G = [N; \mathcal A]$ consists of a finite set $N$ of **nodes** and a set $\mathcal A$ of ordered pairs $(x, y)$ of nodes, the **arcs**, with $x \neq y$ for every arc. There is at most one arc from $x$ to $y$, but both $(x, y)$ and $(y, x)$ may be arcs. Every arc carries a nonnegative real **capacity** $c(x, y) \ge 0$.
--   2. For node sets $X, Y \subseteq N$, $(X, Y)$ is the set of arcs leading from a node of $X$ to a node of $Y$, and for a real function $g$ on the arcs
--   $$g(X, Y) = \sum_{(x, y) \in (X, Y)} g(x, y).$$
--   3. For a function $f$ on the arcs, the **net flow out of** $x$ is $\sum_{y \in A(x)} f(x, y) - \sum_{y \in B(x)} f(y, x)$, where $A(x) = \{y : (x, y) \in \mathcal A\}$ and $B(x) = \{y : (y, x) \in \mathcal A\}$.
--   4. Given two nodes $s$ (the source) and $t$ (the sink), a **static flow of value $v$ from $s$ to $t$** is a function $f$ from $\mathcal A$ to the nonnegative reals such that
--   $$\sum_{y \in A(x)} f(x, y) - \sum_{y \in B(x)} f(y, x) = \begin{cases} v & x = s,\\ 0 & x \neq s, t,\\ -v & x = t,\end{cases} \qquad (2.1)$$
--   $$f(x, y) \le c(x, y) \quad \text{for all } (x, y) \in \mathcal A. \qquad (2.2)$$
--   5. A flow $f$ is **maximal** if it has a value $v$ with $w \le v$ for the value $w$ of every flow from $s$ to $t$.
--   6. A node set $X$ with $s \in X$ and $t \in \bar X = N - X$ determines the **cut** $(X, \bar X)$ separating $s$ and $t$, whose **capacity** is $c(X, \bar X)$. The cut is **minimal** if $c(X, \bar X) \le c(Y, \bar Y)$ for every node set $Y$ with $s \in Y$, $t \notin Y$.
--   7. For a real function $\ell$ on the arcs (§9), a function $f$ on the arcs satisfies (2.1) for a number $v$ and the bounds $\ell(x, y) \le f(x, y) \le c(x, y)$ on every arc (9.2).
--
--   These are the objects of every statement of the mission: the max flow min cut theorem, its corollaries, the integrity theorem, and the lower-bound variant of §9.
--
--   **Formalization Note** Nodes form a `Fintype` with decidable equality, arcs a `Finset (N × N)`. Capacities and flows are functions $N \to N \to \mathbb R$; a flow is required to vanish at every pair that is not an arc, so it is exactly a function on $\mathcal A$, and the values of the capacity off $\mathcal A$ are never used. The value $v$ of a flow is an explicit argument of the flow predicate, as in the book's "flow of value $v$". A cut is encoded by its node set $X$ (a `Finset N`, with $\bar X$ its complement); its arc set is $(X, \bar X)$, and statements that compare cuts as arc sets do so explicitly. Capacities are finite reals: the book's occasional infinite capacities are not used in §§1–9. "Maximal" and "minimal" are explicit predicates, never a supremum or infimum.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 3 (§1, networks), p. 4 (no loops, at most one arc), pp. 7–8 (§2, capacity, static flow (2.1)–(2.2)), p. 16 (§3, (3.1)), p. 17 (§4, cuts), p. 38 and the following page (§9, (9.2)–(9.3))

import Mathlib

namespace FlowsNetworks.MaxFlow

/-- A directed network `[N; 𝒜]` with a capacity function (Ford–Fulkerson, *Flows in Networks*,
Chapter I, §1 p. 3, p. 4, and §2 p. 7). The node set `N` is a finite type; the arc set `𝒜` is a
finite set of ordered pairs, so there is at most one arc from `x` to `y`, while both `(x, y)` and
`(y, x)` may be arcs. Arcs are loop-free (`x ≠ y`, p. 4). Every arc carries a nonnegative real
capacity `c(x, y)` (p. 7); values of `cap` off `𝒜` play no role in any definition below. -/
structure Network (N : Type) [Fintype N] [DecidableEq N] where
  /-- the arc set `𝒜 ⊆ N × N` -/
  arcs : Finset (N × N)
  /-- no arc leads from a node to itself (p. 4) -/
  loopless : ∀ p ∈ arcs, p.1 ≠ p.2
  /-- the capacity function `c` -/
  cap : N → N → ℝ
  /-- capacities are nonnegative reals (p. 7) -/
  cap_nonneg : ∀ p ∈ arcs, 0 ≤ cap p.1 p.2

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The set of arcs `(X, Y)` leading from a node of `X` to a node of `Y` (§3, p. 16). -/
def arcsBetween (G : Network N) (X Y : Finset N) : Finset (N × N) :=
  G.arcs.filter (fun p => p.1 ∈ X ∧ p.2 ∈ Y)

/-- The notation (3.1): `g(X, Y) = ∑_{(x, y) ∈ (X, Y)} g(x, y)` for a function `g` on arcs. -/
def arcSum (G : Network N) (g : N → N → ℝ) (X Y : Finset N) : ℝ :=
  ∑ p ∈ arcsBetween G X Y, g p.1 p.2

/-- The net flow out of `x`: `∑_{y ∈ A(x)} f(x, y) − ∑_{y ∈ B(x)} f(y, x)`, where
`A(x) = {y | (x, y) ∈ 𝒜}` and `B(x) = {y | (y, x) ∈ 𝒜}` (§2, pp. 7–8). -/
def netFlowOut (G : Network N) (f : N → N → ℝ) (x : N) : ℝ :=
  (∑ p ∈ G.arcs.filter (fun p => p.1 = x), f p.1 p.2) -
    ∑ p ∈ G.arcs.filter (fun p => p.2 = x), f p.1 p.2

/-- The equations (2.1): the net flow out of `x` is `v` at `x = s`, `−v` at `x = t`, and `0` at
every other node. -/
def Conservation (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) : Prop :=
  netFlowOut G f s = v ∧ netFlowOut G f t = -v ∧
    ∀ x, x ≠ s → x ≠ t → netFlowOut G f x = 0

/-- A flow is a function on the arcs only: it vanishes at every pair `(x, y) ∉ 𝒜`. -/
def SupportedOnArcs (G : Network N) (f : N → N → ℝ) : Prop :=
  ∀ x y, (x, y) ∉ G.arcs → f x y = 0

/-- A static flow of value `v` from `s` to `t` (§2, p. 7): a function from `𝒜` to the nonnegative
reals satisfying (2.1) and (2.2) `f(x, y) ≤ c(x, y)` for all `(x, y) ∈ 𝒜`. -/
def IsFlow (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) : Prop :=
  SupportedOnArcs G f ∧ (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2) ∧
    (∀ p ∈ G.arcs, f p.1 p.2 ≤ G.cap p.1 p.2) ∧ Conservation G s t f v

/-- A maximal flow from `s` to `t`: a flow whose value is at least the value of every flow from
`s` to `t`. -/
def IsMaxFlow (G : Network N) (s t : N) (f : N → N → ℝ) : Prop :=
  ∃ v, IsFlow G s t f v ∧ ∀ (g : N → N → ℝ) (w : ℝ), IsFlow G s t g w → w ≤ v

/-- The capacity `c(X, X̄)` of the cut `(X, X̄)` determined by the node set `X` (§4, p. 17). -/
def cutCapacity (G : Network N) (X : Finset N) : ℝ :=
  arcSum G G.cap X Xᶜ

/-- `X` determines a minimal cut separating `s` and `t`: `s ∈ X`, `t ∈ X̄`, and `c(X, X̄)` is
least among all cuts `(Y, Ȳ)` with `s ∈ Y`, `t ∈ Ȳ`. -/
def IsMinCut (G : Network N) (s t : N) (X : Finset N) : Prop :=
  s ∈ X ∧ t ∉ X ∧ ∀ Y : Finset N, s ∈ Y → t ∉ Y → cutCapacity G X ≤ cutCapacity G Y

/-- A function `f` on the arcs satisfying (2.1) for the number `v` and the bounds
(9.2) `ℓ(x, y) ≤ f(x, y) ≤ c(x, y)` on every arc (§9, p. 38 and the page after it). -/
def IsBoundedFlow (G : Network N) (ℓ : N → N → ℝ) (s t : N) (f : N → N → ℝ) (v : ℝ) : Prop :=
  SupportedOnArcs G f ∧ (∀ p ∈ G.arcs, ℓ p.1 p.2 ≤ f p.1 p.2) ∧
    (∀ p ∈ G.arcs, f p.1 p.2 ≤ G.cap p.1 p.2) ∧ Conservation G s t f v

end FlowsNetworks.MaxFlow


