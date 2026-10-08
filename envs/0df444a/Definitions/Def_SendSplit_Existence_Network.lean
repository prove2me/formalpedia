-- Prove2me | Definitions.Def_SendSplit_Existence_Network
-- name    : SendSplit_Existence_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:59:26.14854+00:00
-- url     : https://prove2.me/theorems/7c724a1a-fa6e-4941-aecf-f2bd5b5e8d3d
-- title:
--   Section 2 — graphs, preflows, flows, circulations, additive concave flow cost, extreme flows, simple circulations
-- statement:
--   This file fixes the uncapacitated network model of Erickson, Monma and Veinott.
--
--   A **graph** $G = (N, A)$ has the node set $N = \{0, 1, \dots, n-1\}$ and a finite set $A$ of ordered pairs of distinct nodes, the **arcs**. A **preflow** is a nonnegative matrix $x = (x_{ij})$ with $x_{ij} = 0$ whenever $(i,j) \notin A$. Given a **demand vector** $r = (r_i) \in \mathbb{R}^n$ (a negative demand is a supply), a **flow** for $r$ is a preflow satisfying the conservation-of-flow equations
--
--   $$\sum_{(j,i)\in A} x_{ji} \;-\; \sum_{(i,k)\in A} x_{ik} \;=\; r_i \qquad \text{for each node } i,$$
--
--   that is, inflow minus outflow equals demand. A **circulation** is a flow for $r = 0$.
--
--   The **flow cost** of a preflow is additive, $c(x) = \sum_{(i,j)\in A} c_{ij}(x_{ij})$; the standing assumptions on the arc costs are that each $c_{ij}$ is concave on $[0,\infty)$ and $c_{ij}(0) = 0$. A **minimum-cost flow** for $r$ is a flow $x$ for $r$ with $c(x) \le c(x')$ for every flow $x'$ for $r$.
--
--   A preflow **induces** the subgraph consisting of the arcs carrying nonzero flow. A set of arcs is a **forest** if it contains no undirected cycle: no cyclic sequence of $m \ge 2$ distinct nodes $v_0, \dots, v_{m-1}$ and $m$ distinct arcs $e_0, \dots, e_{m-1}$ of the set with $e_k$ joining $v_k$ and $v_{k+1}$ (indices mod $m$) in either direction. In particular two antiparallel arcs $(i,j), (j,i)$ form a cycle of length $2$. An **extreme flow** is a flow whose induced subgraph is a forest.
--
--   A **simple circuit** is a directed cycle $v_0 \to v_1 \to \dots \to v_{m-1} \to v_0$ through $m \ge 2$ distinct nodes whose arcs all lie in $A$; its arc set is $C = \{(v_k, v_{k+1})\}$. A **simple circulation** (an extreme direction-of-recession of the set of flows) is a circulation whose induced subgraph is a simple circuit; it has equal flows on the arcs of the circuit.
--
--   These are the objects of Theorem 1 and of every milestone of the mission.
--
--   **Formalization Note** Nodes are `Fin n`; the graph is the structure `ArcGraph n` carrying `A : Finset (Fin n × Fin n)` and the proof that no arc is a loop. Preflows and costs are full matrices `Fin n → Fin n → ℝ` and `Fin n → Fin n → ℝ → ℝ`; only entries on arcs matter. The paper assumes $c_{ij}(0) = 0$ "without loss of generality and without further mention"; here it is part of `IsConcaveArcCost`, which every theorem takes as a hypothesis. Forests are taken over arcs, not over a simple graph built from the support, so antiparallel arcs count as a cycle.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 638, Section 2

import Mathlib

namespace SendSplit.Existence

/-- A directed graph `G = (N, A)` on the node set `N = Fin n`: a finite set `A` of ordered pairs
of distinct nodes, called arcs (Erickson–Monma–Veinott 1987, p. 638). -/
structure ArcGraph (n : ℕ) where
  /-- The arcs. -/
  A : Finset (Fin n × Fin n)
  /-- Arcs join distinct nodes. -/
  loopless : ∀ p ∈ A, p.1 ≠ p.2

variable {n : ℕ}

/-- A preflow: a nonnegative matrix `x = (x i j)` carried by the arcs (zero off `A`). -/
def IsPreflow (G : ArcGraph n) (x : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ ∀ i j, (i, j) ∉ G.A → x i j = 0

/-- A flow for the demand vector `r`: a preflow with inflow minus outflow equal to `r i`
at every node `i`. -/
def IsFlow (G : ArcGraph n) (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) : Prop :=
  IsPreflow G x ∧
    ∀ i, (∑ j ∈ Finset.univ.filter (fun j => (j, i) ∈ G.A), x j i)
        - (∑ k ∈ Finset.univ.filter (fun k => (i, k) ∈ G.A), x i k) = r i

/-- A circulation: a flow for the zero demand vector. -/
def IsCirculation (G : ArcGraph n) (x : Fin n → Fin n → ℝ) : Prop :=
  IsFlow G (fun _ => 0) x

/-- The additive flow cost `c(x) = ∑_{(i,j) ∈ A} c_ij(x_ij)`. -/
def flowCost (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (x : Fin n → Fin n → ℝ) : ℝ :=
  ∑ p ∈ G.A, c p.1 p.2 (x p.1 p.2)

/-- The standing assumptions on the arc costs: each `c_ij` is concave on `[0, ∞)` and
`c_ij(0) = 0`. -/
def IsConcaveArcCost (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) : Prop :=
  ∀ p ∈ G.A, ConcaveOn ℝ (Set.Ici 0) (c p.1 p.2) ∧ c p.1 p.2 0 = 0

/-- A minimum-cost flow for `r`: a flow for `r` whose cost is at most that of every flow
for `r`. -/
def IsMinCostFlow (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (x : Fin n → Fin n → ℝ) : Prop :=
  IsFlow G r x ∧ ∀ x', IsFlow G r x' → flowCost G c x ≤ flowCost G c x'

/-- The arcs of the subgraph induced by a preflow: the arcs carrying nonzero flow. -/
noncomputable def support (G : ArcGraph n) (x : Fin n → Fin n → ℝ) : Finset (Fin n × Fin n) :=
  G.A.filter (fun p => x p.1 p.2 ≠ 0)

/-- A set `F` of arcs is a forest (in the undirected sense, over arcs): there is no undirected
cycle, i.e. no cyclic sequence of `m + 2 ≥ 2` distinct nodes `v 0, …, v (m+1)` and distinct arcs
`e 0, …, e (m+1)` of `F` such that each `e k` joins `v k` and `v (k+1)` (indices mod `m + 2`) in
either direction. A pair of antiparallel arcs `(i, j), (j, i)` in `F` is a cycle of length 2. -/
def IsForest (F : Finset (Fin n × Fin n)) : Prop :=
  ¬ ∃ (m : ℕ) (v : Fin (m + 2) → Fin n) (e : Fin (m + 2) → Fin n × Fin n),
    Function.Injective v ∧ Function.Injective e ∧
      ∀ k, e k ∈ F ∧ (e k = (v k, v (k + 1)) ∨ e k = (v (k + 1), v k))

/-- An extreme flow for `r`: a flow for `r` whose induced subgraph is a forest. -/
def IsExtremeFlow (G : ArcGraph n) (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) : Prop :=
  IsFlow G r x ∧ IsForest (support G x)

/-- `C` is the arc set of a simple circuit of `G`: there are `m + 2 ≥ 2` distinct nodes
`v 0, …, v (m+1)` with every `(v k, v (k+1))` an arc (indices mod `m + 2`), and `C` is the set
of these arcs. -/
def IsSimpleCircuit (G : ArcGraph n) (C : Finset (Fin n × Fin n)) : Prop :=
  ∃ (m : ℕ) (v : Fin (m + 2) → Fin n), Function.Injective v ∧
    (∀ k, (v k, v (k + 1)) ∈ G.A) ∧ C = Finset.univ.image (fun k => (v k, v (k + 1)))

/-- A simple circulation (extreme direction-of-recession): a circulation whose induced
subgraph is a simple circuit. -/
def IsSimpleCirculation (G : ArcGraph n) (y : Fin n → Fin n → ℝ) : Prop :=
  IsCirculation G y ∧ IsSimpleCircuit G (support G y)

end SendSplit.Existence


