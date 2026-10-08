-- Prove2me | Definitions.Def_SendSplit_DPEquations_Network
-- name    : SendSplit_DPEquations_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:00:12.380549+00:00
-- url     : https://prove2.me/theorems/a9917146-46f9-44ba-a4c3-4f8e68be6ae9
-- title:
--   Section 2 — graph, preflows, flows, additive concave flow cost with c_ij(0) = 0, minimum-cost flows, simple circulations
-- statement:
--   This file fixes the uncapacitated network model of Erickson, Monma and Veinott (Section 2).
--
--   A **(directed) graph** $G = (N, A)$ has the node set $N = \{0, 1, \dots, n-1\}$ and a set $A$ of arcs, which are ordered pairs $(i, j)$ of *distinct* nodes. A **preflow** is a nonnegative matrix $x = (x_{ij})$, where $x_{ij}$ is the number of units flowing from $i$ to $j$ along the arc $(i, j)$; it vanishes on pairs that are not arcs. Given a **demand vector** $r = (r_i)$, with $r_i \in \mathbb{R}$ the demand at node $i$ (a negative demand is a supply), a **flow** for $r$ is a preflow satisfying conservation of flow,
--
--   $$\sum_{(j,i)\in A} x_{ji} \;-\; \sum_{(i,k)\in A} x_{ik} \;=\; r_i \qquad \text{for each } i \in N .$$
--
--   The arc costs are functions $c_{ij} : \mathbb{R} \to \mathbb{R}$, each **concave on the nonnegative half-line** and with $c_{ij}(0) = 0$. The **cost** of a preflow is $c(x) = \sum_{(i,j)\in A} c_{ij}(x_{ij})$. A **minimum-cost flow** for $r$ is a flow $x$ with $c(x) \le c(y)$ for every flow $y$ for $r$.
--
--   A **simple circulation** is a circulation (a flow for the zero demand vector) whose induced subgraph is a simple circuit: there are $m \ge 2$ distinct nodes $v_0, \dots, v_{m-1}$ such that $(v_0, v_1), \dots, (v_{m-2}, v_{m-1}), (v_{m-1}, v_0)$ are arcs, and the matrix equals a common value $\theta > 0$ on these arcs and $0$ elsewhere.
--
--   These objects are the substrate of every statement of the mission: the subproblem minimum costs $C_{iI}$, the send-and-split equations, and Theorem 2.
--
--   **Formalization Note** Nodes are `Fin n`, arcs a `Finset (Fin n × Fin n)`. Looplessness (`IsGraph`) and the cost assumptions (`IsConcaveArcCost`: concavity on `Set.Ici 0` and $c_{ij}(0) = 0$ for every arc) are predicates that every theorem takes as hypotheses. The paper assumes $c_{ij}(0) = 0$ "without loss of generality and without further mention" (p. 638); it is stated explicitly here. Only the values of $c_{ij}$ on $[0, \infty)$ at arcs ever matter.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 638, Section 2

import Mathlib

namespace SendSplit.DPEquations

/-- Section 2 (p. 638): a (directed) graph `G = (N, A)` on the nodes `N = Fin n` whose arcs
`A` are ordered pairs of *distinct* nodes. -/
def IsGraph {n : ℕ} (A : Finset (Fin n × Fin n)) : Prop :=
  ∀ p ∈ A, p.1 ≠ p.2

/-- A preflow is a nonnegative matrix `x = (x_ij)`; it carries flow only on arcs of `A`. -/
def IsPreflow {n : ℕ} (A : Finset (Fin n × Fin n)) (x : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ ∀ i j, (i, j) ∉ A → x i j = 0

/-- A flow for the demand vector `r` is a preflow satisfying conservation of flow:
inflow minus outflow at node `i` equals the demand `r i`, for every node `i`. -/
def IsFlow {n : ℕ} (A : Finset (Fin n × Fin n)) (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) :
    Prop :=
  IsPreflow A x ∧
    ∀ i : Fin n,
      (∑ j ∈ Finset.univ.filter (fun j => (j, i) ∈ A), x j i)
        - (∑ k ∈ Finset.univ.filter (fun k => (i, k) ∈ A), x i k) = r i

/-- Standing assumption on the arc costs (p. 638): each `c_ij` is concave on the nonnegative
half-line and `c_ij(0) = 0` ("without loss of generality and without further mention"). -/
def IsConcaveArcCost {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ) :
    Prop :=
  ∀ p ∈ A, ConcaveOn ℝ (Set.Ici 0) (c p.1 p.2) ∧ c p.1 p.2 0 = 0

/-- The additive flow cost `c(x) = Σ_{(i,j) ∈ A} c_ij(x_ij)`. -/
def flowCost {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ)
    (x : Fin n → Fin n → ℝ) : ℝ :=
  ∑ p ∈ A, c p.1 p.2 (x p.1 p.2)

/-- A minimum-cost flow for the demand vector `r`: a flow whose cost is at most the cost of
every flow for `r`. -/
def IsMinCostFlow {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ)
    (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) : Prop :=
  IsFlow A r x ∧ ∀ y, IsFlow A r y → flowCost A c x ≤ flowCost A c y

/-- A simple circulation (p. 638): a circulation whose induced subgraph is a simple circuit,
i.e. there are `m ≥ 2` distinct nodes `v 0, …, v (m-1)` with arcs
`(v k, v (k+1 mod m)) ∈ A`, and the matrix equals a common value `θ > 0` on these arcs and
`0` elsewhere. -/
def IsSimpleCirculation {n : ℕ} (A : Finset (Fin n × Fin n)) (y : Fin n → Fin n → ℝ) :
    Prop :=
  ∃ (m : ℕ) (v : Fin m → Fin n) (θ : ℝ), 2 ≤ m ∧ Function.Injective v ∧ 0 < θ ∧
    (∀ k : Fin m, (v k, v (finRotate m k)) ∈ A) ∧
    ∀ i j, y i j = if ∃ k : Fin m, v k = i ∧ v (finRotate m k) = j then θ else 0

end SendSplit.DPEquations


