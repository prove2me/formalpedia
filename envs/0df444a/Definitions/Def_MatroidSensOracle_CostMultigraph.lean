-- Prove2me | Definitions.Def_MatroidSensOracle_CostMultigraph
-- name    : MatroidSensOracle_CostMultigraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:44.824199+00:00
-- url     : https://prove2.me/theorems/e003c14b-5f64-463f-8bf6-a6a8a28a7db3
-- title:
--   Directed multigraphs with unit capacities and integer costs: flows, $\lambda_G(s,t)$, min-cost flows, cuts, nearest min-cut, residual graph
-- statement:
--   A **cost multigraph** on a vertex set $V$ has edges $e=1,\dots,m$, each with a tail, a head (via the published `CombOpt.MinCostFlow.Digraph`; loops and parallel edges allowed) and an integer cost $c(e)$. Every edge has capacity $1$.
--
--   1. An **$(s,t)$-flow** is $h:E\to\{0,1\}$ with in-flow equal to out-flow at every vertex other than $s$ and $t$. Its value $\mathrm{val}(h)$ is the net out-flow of $s$, and its cost is $\sum_e c(e)h(e)$.
--   2. $\lambda_G(s,t)$ is the maximum value of an $(s,t)$-flow.
--   3. The **minimum cost of a flow of value $v$** is the least cost of an $(s,t)$-flow of value $v$ (cycles, also of negative cost, allowed), or $+\infty$ if there is none.
--   4. An **$(s,t)$-cut** is given by its source side $A$ with $s\in A$, $t\notin A$; its capacity is the number of edges from $A$ to $V\setminus A$. A **min-cut** has the least capacity, and the **nearest min-cut** $\mathrm{NMC}_G(s,t)$ is the min-cut whose source side is contained in the source side of every min-cut.
--   5. The **residual graph** $G_h$ reverses each edge with $h(e)=1$ and negates its cost.
--
--   Edges are inserted as new edges (`addEdges`) and an update $(I,F)$ deletes the edges $F$ and appends the edges $I$ (`apply`).
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), §2, p.12 (PDF p.15)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph

set_option autoImplicit false

namespace MatroidSensOracle

/-!
# Directed multigraphs with unit capacities and integer costs; flows, cuts, nearest min-cuts

Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), §2, p.12 (PDF p.15):
"Let G = (V, E) be a directed graph with unit edge capacities with a cost function
c : E → {−W, …, W}. […] For a pair s, t ∈ V, we use λ_G(s, t) to denote the maximum value of an
(s, t)-flow in G. An (s, t)-cut C partitions the vertex set into (A_C, B_C) with s ∈ A_C and
t ∈ B_C; its capacity is the number of edges directed from A_C to B_C, and an (s, t)-min-cut is one
with minimum capacity […]. Given an (s, t)-flow h in G, the residual graph G_h is obtained from G by
reversing every edge that carries flow under h, i.e., replacing each edge e = (u, v) with h(e) = 1 by
its reverse e_rev = (v, u), where c(e_rev) = −c(e). […] An (s, t)-min-cut C∗ is said to be the
nearest min-cut if for each (s, t)-min-cut C we have A_{C∗} ⊆ A_C."

**Formalization Note.**
* A multigraph has `m` edges `Fin m`, with tail and head given by the published
  `CombOpt.MinCostFlow.Digraph` (loops and parallel edges allowed) and an integer cost per edge.
* Capacities are `1`, so a flow is `h : Fin m → Bool` (`h e = true` means `h(e) = 1`) with
  conservation (in-flow = out-flow) at every vertex other than `s` and `t`. Its value is the net
  out-flow of `s`, in `ℤ`. Its cost is `∑_e c(e) h(e)`.
* `maxFlow G s t = λ_G(s, t)` is the largest value of a flow (a maximum over the finitely many flows;
  the zero flow has value `0`, so the set is nonempty and bounded).
* `minCostFlow G s t v ∈ ℤ ∪ {⊤}` is the least cost of a flow of value `v` (`⊤` if there is none).
  Flows may contain cycles, also of negative cost.
* A cut is its source side `A` (a finite vertex set with `s ∈ A`, `t ∉ A`); its capacity counts the
  edges from `A` to its complement.
-/

/-- A directed multigraph on the vertex type `V` with `m` edges, unit capacities and integer
costs. -/
structure CostMultigraph (V : Type) where
  m : ℕ
  arcs : CombOpt.MinCostFlow.Digraph V (Fin m)
  cost : Fin m → ℤ

namespace CostMultigraph

variable {V : Type}

/-- The multigraph whose edges are the triples `(tail, head, cost)` of a list, in order. -/
def ofList (l : List (V × V × ℤ)) : CostMultigraph V where
  m := l.length
  arcs := ⟨fun e => (l.get e).1, fun e => (l.get e).2.1⟩
  cost := fun e => (l.get e).2.2

/-- The edge `e` as a triple `(tail, head, cost)`. -/
def edge (G : CostMultigraph V) (e : Fin G.m) : V × V × ℤ := (G.arcs.tail e, G.arcs.head e, G.cost e)

/-- The edges of `G` as a list of triples, in order. -/
def toList (G : CostMultigraph V) : List (V × V × ℤ) := List.ofFn G.edge

/-- `G` with the edges `l` appended as new edges (parallel to existing ones if they repeat a pair). -/
def addEdges (G : CostMultigraph V) (l : List (V × V × ℤ)) : CostMultigraph V := ofList (G.toList ++ l)

/-- `G + (I, F)`: delete the edges `F` (by index) and insert the edges `I` as new edges. The
remaining edges keep their order and the inserted ones come after them. -/
def apply (G : CostMultigraph V) (I : List (V × V × ℤ)) (F : Finset (Fin G.m)) : CostMultigraph V :=
  ofList ((((List.finRange G.m).filter fun e => e ∉ F).map G.edge) ++ I)

/-- The multigraph with its vertices renamed by `φ`. -/
def mapVert {V' : Type} (φ : V → V') (G : CostMultigraph V) : CostMultigraph V' where
  m := G.m
  arcs := ⟨fun e => φ (G.arcs.tail e), fun e => φ (G.arcs.head e)⟩
  cost := G.cost

variable [DecidableEq V]

/-- Number of edges carrying flow into `v`. -/
def inflow (G : CostMultigraph V) (h : Fin G.m → Bool) (v : V) : ℕ :=
  (Finset.univ.filter fun e => h e = true ∧ G.arcs.head e = v).card

/-- Number of edges carrying flow out of `v`. -/
def outflow (G : CostMultigraph V) (h : Fin G.m → Bool) (v : V) : ℕ :=
  (Finset.univ.filter fun e => h e = true ∧ G.arcs.tail e = v).card

/-- `h` is an `(s, t)`-flow: 0/1 on every edge, conserved at every vertex other than `s`, `t`. -/
def IsFlow (G : CostMultigraph V) (s t : V) (h : Fin G.m → Bool) : Prop :=
  ∀ v, v ≠ s → v ≠ t → G.inflow h v = G.outflow h v

/-- The value of a flow: the net out-flow of `s`. -/
def value (G : CostMultigraph V) (s : V) (h : Fin G.m → Bool) : ℤ :=
  (G.outflow h s : ℤ) - G.inflow h s

/-- The cost `∑_e c(e) h(e)` of a flow. -/
def flowCost (G : CostMultigraph V) (h : Fin G.m → Bool) : ℤ :=
  ∑ e, if h e = true then G.cost e else 0

/-- `λ_G(s, t)`: the maximum value of an `(s, t)`-flow. -/
noncomputable def maxFlow (G : CostMultigraph V) (s t : V) : ℕ :=
  sSup {k : ℕ | ∃ h, G.IsFlow s t h ∧ G.value s h = k}

open Classical in
/-- The minimum cost of an `(s, t)`-flow of value `v` (`⊤` if no flow has value `v`). -/
noncomputable def minCostFlow (G : CostMultigraph V) (s t : V) (v : ℤ) : WithTop ℤ :=
  (Finset.univ.filter fun h => G.IsFlow s t h ∧ G.value s h = v).inf fun h => (G.flowCost h : WithTop ℤ)

/-- The residual graph `G_h`: every edge carrying flow is reversed and its cost negated; the edge
indices are kept, so edge `e` of `G_h` is `e` or `e_rev`. -/
def residual (G : CostMultigraph V) (h : Fin G.m → Bool) : CostMultigraph V where
  m := G.m
  arcs := ⟨fun e => if h e then G.arcs.head e else G.arcs.tail e,
    fun e => if h e then G.arcs.tail e else G.arcs.head e⟩
  cost := fun e => if h e then -G.cost e else G.cost e

/-- The capacity of the cut with source side `A`: the number of edges from `A` to its complement. -/
def cutCapacity (G : CostMultigraph V) (A : Finset V) : ℕ :=
  (Finset.univ.filter fun e => G.arcs.tail e ∈ A ∧ G.arcs.head e ∉ A).card

/-- `A` is the source side of an `(s, t)`-min-cut. -/
def IsMinCut (G : CostMultigraph V) (s t : V) (A : Finset V) : Prop :=
  s ∈ A ∧ t ∉ A ∧ ∀ A' : Finset V, s ∈ A' → t ∉ A' → G.cutCapacity A ≤ G.cutCapacity A'

/-- `A` is the source side of the nearest `(s, t)`-min-cut `NMC_G(s, t)`: a min-cut whose source
side is contained in the source side of every min-cut. -/
def IsNearestMinCut (G : CostMultigraph V) (s t : V) (A : Finset V) : Prop :=
  G.IsMinCut s t A ∧ ∀ A' : Finset V, G.IsMinCut s t A' → A ⊆ A'

end CostMultigraph

end MatroidSensOracle


