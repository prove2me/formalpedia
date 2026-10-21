-- Prove2me | Definitions.Def_FlowsNetworks_MultiTerminal_UndirectedNetwork
-- name    : FlowsNetworks_MultiTerminal_UndirectedNetwork
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:24.852862+00:00
-- url     : https://prove2.me/theorems/e1c7c18e-4a59-43be-bc18-f204df849cc9
-- title:
--   Undirected networks, flows, maximal flow values, flow functions, minimal cuts and the condensed network
-- statement:
--   Following Chapter I (§§1–2, §10) and Chapter IV (§§2–3) of Ford and Fulkerson's *Flows in Networks*, this file sets up the objects of the multi-terminal theory.
--
--   1. An **undirected network** $G$ on a finite node set $N$ is an undirected graph on $N$ (no loops, at most one arc joining two nodes) whose arcs $\{x, y\}$ carry **capacities** $c(x, y) = c(y, x) \ge 0$.
--   2. A **flow of value $w$ from $s$ to $t$** is a function $f(x, y) \ge 0$ on ordered pairs, the flow from $x$ to $y$, vanishing unless $\{x, y\}$ is an arc, such that on every arc (constraints (10.1) of Chapter I)
--   $$f(x, y) \le c(x, y), \qquad f(y, x) \le c(x, y), \qquad f(x, y)\, f(y, x) = 0,$$
--   and the net flow out of a node, $f(x, N) - f(N, x)$, is $w$ at $x = s$, $-w$ at $x = t$, and $0$ at every other node.
--   3. $w$ is the **maximal flow value** from $s$ to $t$ if some flow from $s$ to $t$ has value $w$ and no flow from $s$ to $t$ has larger value.
--   4. A function $v$ is the **flow function** of $G$ if, for all distinct nodes $x \neq y$, $v(x, y)$ is the maximal flow value from $x$ to $y$. The book leaves $v(x, x)$ undefined; diagonal values are unconstrained.
--   5. For a node set $X$ with complement $\bar X = N - X$, the **cut capacity** $c(X, \bar X)$ is the sum of $c(x, y)$ over the arcs joining a node $x \in X$ to a node $y \in \bar X$. $(X, \bar X)$ is a **minimal cut separating $s$ and $t$** if $s \in X$, $t \in \bar X$, and $c(X, \bar X) \le c(Y, \bar Y)$ for every $Y$ with $s \in Y$, $t \notin Y$.
--   6. The **condensed network** of $G$ with respect to $X$ has as nodes the **ordinary nodes** $x \in X$ together with one new node standing for all of $\bar X$. Two ordinary nodes are joined, with capacity $c(x, y)$, exactly when they are joined in $G$; an ordinary node $x$ is joined to the condensed node exactly when $G$ has an arc from $x$ to some node of $\bar X$, and the capacity of that arc is
--   $$\sum_{y \in \bar X,\ \{x, y\} \text{ an arc}} c(x, y).$$
--
--   These are the objects of Lemma 2.1, Lemma 2.2, Theorem 2.1 (realizability of flow functions by trees) and Lemma 3.1 (condensing one side of a minimal cut).
--
--   **Formalization Note** Nodes form a `Fintype` with decidable equality; arcs are a Mathlib `SimpleGraph`. Capacities are finite nonnegative reals on arcs. The maximal flow value is an attained maximum (`IsGreatest`), never a bare supremum. The node set of the condensed network is `Option X`: `some x` is the ordinary node $x$, `none` the condensed node $\bar X$. A cut is encoded by its node set $X$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, pp. 3–8 (§§1–2, networks, flows, Eq. (2.1)), p. 40 (§10, undirected arcs, Eq. (10.1)); Chapter IV, p. 1 (undirected networks), p. 6 (§2, flow function), pp. 9–10 (§3, minimal cut, condensed network, ordinary nodes)

import Mathlib

namespace FlowsNetworks.MultiTerminal

/-- An undirected network (Ford–Fulkerson, *Flows in Networks*, Chapter I, §§1–2, pp. 3–7, and
§10, p. 40; Chapter IV, p. 1). The node set `N` is a finite type; the arcs form a simple graph on
`N`: undirected, without loops, at most one arc joining two nodes. Every arc `(x, y)` carries a
nonnegative real capacity `c(x, y) = c(y, x)`; values of `cap` at pairs that are not arcs play no
role in any definition below. -/
structure UNetwork (N : Type) [Fintype N] [DecidableEq N] where
  /-- the undirected arcs -/
  graph : SimpleGraph N
  /-- the capacity function `c` -/
  cap : N → N → ℝ
  /-- an undirected arc has one capacity, `c(x, y) = c(y, x)` -/
  cap_symm : ∀ x y, cap x y = cap y x
  /-- capacities of arcs are nonnegative reals (Chapter I, p. 7 and §10, p. 40) -/
  cap_nonneg : ∀ x y, graph.Adj x y → 0 ≤ cap x y

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The net flow out of the node `x`, `f(x, N) − f(N, x)`, for a function `f` on ordered pairs
(`f(x, y)` is the flow from `x` to `y`). -/
def netFlowOut (f : N → N → ℝ) (x : N) : ℝ :=
  (∑ y, f x y) - ∑ y, f y x

/-- `f` is a flow of value `w` from `s` to `t` in the undirected network `G` (Chapter I, §2,
equations (2.1), and §10, constraints (10.1)): `f(x, y) ≥ 0` is the flow from `x` to `y`; it vanishes
unless `(x, y)` is an arc; on an arc, `f(x, y) ≤ c(x, y)`, `f(y, x) ≤ c(x, y)` and
`f(x, y) · f(y, x) = 0` (flow in only one direction); and the net flow out of a node is `w` at `s`,
`−w` at `t`, and `0` at every other node. -/
def IsFlow (G : UNetwork N) (s t : N) (f : N → N → ℝ) (w : ℝ) : Prop :=
  (∀ x y, ¬ G.graph.Adj x y → f x y = 0) ∧
  (∀ x y, 0 ≤ f x y) ∧
  (∀ x y, G.graph.Adj x y →
    f x y ≤ G.cap x y ∧ f y x ≤ G.cap x y ∧ f x y * f y x = 0) ∧
  netFlowOut f s = w ∧ netFlowOut f t = -w ∧
  ∀ x, x ≠ s → x ≠ t → netFlowOut f x = 0

/-- `w` is the maximal flow value from `s` to `t` in `G`: some flow from `s` to `t` has value `w`,
and every flow from `s` to `t` has value at most `w` (the maximum is attained). -/
def IsMaxFlowValue (G : UNetwork N) (s t : N) (w : ℝ) : Prop :=
  IsGreatest {u : ℝ | ∃ f : N → N → ℝ, IsFlow G s t f u} w

/-- `v` is the flow (value) function of `G` (Chapter IV, §2, p. 6): for every two distinct nodes
`x ≠ y`, `v(x, y)` is the maximal flow value from `x` to `y` in `G`. The diagonal values `v(x, x)`
are left undefined in the book and are unconstrained here. -/
def IsFlowFunction (G : UNetwork N) (v : N → N → ℝ) : Prop :=
  ∀ x y : N, x ≠ y → IsMaxFlowValue G x y (v x y)

open Classical in
/-- The capacity `c(X, X̄)` of the cut determined by the node set `X`: the sum of `c(x, y)` over
the arcs joining a node `x ∈ X` to a node `y ∈ X̄ = N − X`. -/
noncomputable def cutCap (G : UNetwork N) (X : Finset N) : ℝ :=
  ∑ x ∈ X, ∑ y ∈ Xᶜ, if G.graph.Adj x y then G.cap x y else 0

/-- `(X, X̄)` is a minimal cut separating `s` and `t` (an `s, t` minimal cut): `s ∈ X`, `t ∈ X̄`,
and `c(X, X̄) ≤ c(Y, Ȳ)` for every node set `Y` with `s ∈ Y`, `t ∉ Y`. -/
def IsMinCut (G : UNetwork N) (s t : N) (X : Finset N) : Prop :=
  s ∈ X ∧ t ∉ X ∧ ∀ Y : Finset N, s ∈ Y → t ∉ Y → cutCap G X ≤ cutCap G Y

open Classical in
/-- The capacity of the single arc joining the ordinary node `x ∈ X` to the condensed node `X̄` in
the condensed network: the sum of the capacities of all arcs of `G` joining `x` to a node of
`X̄` (several arcs joining the same pair of nodes are replaced by one arc, Chapter IV, §3, p. 10). -/
noncomputable def capToComplement (G : UNetwork N) (X : Finset N) (x : N) : ℝ :=
  ∑ y ∈ Xᶜ, if G.graph.Adj x y then G.cap x y else 0

/-- The arcs of the condensed network (Chapter IV, §3, p. 10): two ordinary nodes `x, y ∈ X` are
joined iff they are joined in `G`; an ordinary node `x` is joined to the condensed node (`none`)
iff `G` has an arc joining `x` to some node of `X̄`. -/
def condensedAdj (G : UNetwork N) (X : Finset N) : Option X → Option X → Prop
  | some x, some y => G.graph.Adj x y
  | some x, none => ∃ y, y ∉ X ∧ G.graph.Adj x y
  | none, some y => ∃ x, x ∉ X ∧ G.graph.Adj y x
  | none, none => False

/-- The capacities of the condensed network: `c(x, y)` between ordinary nodes, and the summed
capacity `capToComplement` between an ordinary node and the condensed node. -/
noncomputable def condensedCap (G : UNetwork N) (X : Finset N) : Option X → Option X → ℝ
  | some x, some y => G.cap x y
  | some x, none => capToComplement G X x
  | none, some y => capToComplement G X y
  | none, none => 0

/-- The condensed network (Chapter IV, §3, p. 10): all nodes of `X̄ = N − X` are condensed into a
single node, to which all the arcs of the cut `(X, X̄)` are attached, several arcs joining the same
pair of nodes being replaced by a single arc whose capacity is the sum of theirs. Its node set is
`Option X`: `some x` is the ordinary node `x ∈ X`, and `none` is the condensed node `X̄`. -/
noncomputable def condense (G : UNetwork N) (X : Finset N) : UNetwork (Option X) where
  graph :=
    { Adj := condensedAdj G X
      symm := ⟨by
        intro a b h
        rcases a with _ | x <;> rcases b with _ | y <;>
          simp only [condensedAdj] at h ⊢
        · exact h
        · exact h
        · exact G.graph.adj_symm h⟩
      loopless := ⟨by
        intro a h
        rcases a with _ | x
        · exact h
        · exact G.graph.loopless.irrefl _ h⟩ }
  cap := condensedCap G X
  cap_symm := by
    intro a b
    rcases a with _ | x <;> rcases b with _ | y <;> simp only [condensedCap]
    exact G.cap_symm _ _
  cap_nonneg := by
    intro a b _
    rcases a with _ | x <;> rcases b with _ | y <;> simp only [condensedCap, le_refl]
    · exact Finset.sum_nonneg fun z _ => by
        split_ifs with h
        · exact G.cap_nonneg _ _ h
        · exact le_refl 0
    · exact Finset.sum_nonneg fun z _ => by
        split_ifs with h
        · exact G.cap_nonneg _ _ h
        · exact le_refl 0
    · exact G.cap_nonneg _ _ ‹_›

end FlowsNetworks.MultiTerminal


