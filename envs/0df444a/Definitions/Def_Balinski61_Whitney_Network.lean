-- Prove2me | Definitions.Def_Balinski61_Whitney_Network
-- name    : Balinski61_Whitney_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:43:51.576534+00:00
-- url     : https://prove2.me/theorems/953db4c1-4f7a-46a7-beec-6ce1d89c2fe0
-- title:
--   Networks with point and line capacities: path flows, flows, disconnecting sets (p. 433)
-- statement:
--   Following Balinski (p. 433), a **network** is a connected graph $G$ in which every point $x$ carries a nonnegative capacity $c(x)$ and every line $e$ a nonnegative capacity $c(e)$, with two distinguished points, the **source** $p_s$ and the **sink** $p_k$.
--
--   1. A **path flow** is a pair $(C,t)$ of a path $C$ from $p_s$ to $p_k$ and a number $t \ge 0$. A **flow** assigns a number $f(C) \ge 0$ to every path $C$ from $p_s$ to $p_k$ such that, for every point $x$ and every line $e$,
--   $$
--   \sum_{C \ni x} f(C) \le c(x), \qquad \sum_{C \ni e} f(C) \le c(e),
--   $$
--   the sums running over the paths that go through $x$, resp. through $e$.
--   2. The **value** of a flow is $\sum_C f(C)$.
--   3. A **disconnecting set** is a pair $(X, F)$ of a finite set $X$ of points and a finite set $F$ of lines of $G$ such that every walk from $p_s$ to $p_k$ passes through a point of $X$ or uses a line of $F$. Its **value** is
--   $$
--   \sum_{x \in X} c(x) + \sum_{e \in F} c(e).
--   $$
--
--   These are the objects of the max-flow min-cut theorem with capacities on both points and lines, which Balinski uses to prove Whitney's theorem.
--
--   **Formalization Note** The capacities are functions $V \to \mathbb R$ and $\mathrm{Sym2}\,V \to \mathbb R$ (only the values on lines of $G$ matter); nonnegativity, connectivity of $G$ and $p_s \ne p_k$ are hypotheses of the theorems, not part of this file. A flow is a function on the finite type `G.Path ps pk` of simple paths; the paper's "collection of path flows" may repeat a path or use a path with repeated points, but merging repeated path flows and shortcutting a path to a simple one with fewer points and lines changes neither feasibility nor value, so the maximum value is the same. Every point carries a capacity, including $p_s$ and $p_k$, and a disconnecting set may contain $p_s$ or $p_k$, exactly as the definitions on the page read.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 433: definitions of network, path flow, flow, value of a flow, disconnecting set and its value

import Mathlib

namespace Balinski61.Whitney

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The sum of the numbers of all path flows of `f` that go through the point `x` (p. 433): a
path flow `(C, f C)` goes through `x` when `x` is one of the points of `C`. -/
def loadV {ps pk : V} (f : G.Path ps pk → ℝ) (x : V) : ℝ :=
  ∑ C ∈ Finset.univ.filter (fun C : G.Path ps pk => x ∈ (C : G.Walk ps pk).support), f C

/-- The sum of the numbers of all path flows of `f` that go through the line `e` (p. 433). -/
def loadE {ps pk : V} (f : G.Path ps pk → ℝ) (e : Sym2 V) : ℝ :=
  ∑ C ∈ Finset.univ.filter (fun C : G.Path ps pk => e ∈ (C : G.Walk ps pk).edges), f C

/-- A **flow** from `ps` to `pk` in the network `(G, capV, capE)` (p. 433): a nonnegative number
`f C` on every path `C` from `ps` to `pk` (the path flow `(C, f C)`), such that the sum of the
numbers of all path flows through any one point, resp. line, of `G` is not greater than the
capacity of that point, resp. line. -/
def IsFlow (capV : V → ℝ) (capE : Sym2 V → ℝ) (ps pk : V) (f : G.Path ps pk → ℝ) : Prop :=
  (∀ C, 0 ≤ f C) ∧ (∀ x, loadV G f x ≤ capV x) ∧ (∀ e ∈ G.edgeSet, loadE G f e ≤ capE e)

/-- The **value** of a flow (p. 433): the sum of the numbers of all its path flows. -/
def flowValue {ps pk : V} (f : G.Path ps pk → ℝ) : ℝ :=
  ∑ C, f C

/-- A **disconnecting set** (p. 433): a set `X` of points and a set `F` of lines of `G` which
disconnect `ps` and `pk`, i.e. every walk from `ps` to `pk` in `G` passes through a point of `X`
or uses a line of `F`. -/
def IsDisconnecting (ps pk : V) (X : Finset V) (F : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ F, e ∈ G.edgeSet) ∧
    ∀ C : G.Walk ps pk, (∃ x ∈ X, x ∈ C.support) ∨ (∃ e ∈ F, e ∈ C.edges)

/-- The **value** of a disconnecting set `(X, F)` (p. 433): the sum of the capacities of the
points and lines which make up that set. -/
def cutValue (capV : V → ℝ) (capE : Sym2 V → ℝ) (X : Finset V) (F : Finset (Sym2 V)) : ℝ :=
  ∑ x ∈ X, capV x + ∑ e ∈ F, capE e

end Balinski61.Whitney


