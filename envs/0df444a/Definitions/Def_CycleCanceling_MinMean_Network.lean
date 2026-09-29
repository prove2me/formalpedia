-- Prove2me | Definitions.Def_CycleCanceling_MinMean_Network
-- name    : CycleCanceling_MinMean_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:09:45.151994+00:00
-- url     : https://prove2.me/theorems/e571d004-49d9-420d-b871-0ede20c3e7c4
-- title:
--   Circulation networks, circulations (1)–(3), cost, residual cycles and mean cost
-- statement:
--   This file fixes the framework of Goldberg and Tarjan's Section 2.
--
--   1. A **circulation network** is a directed graph $G=(V,E)$ on a finite vertex set $V$ with $n=|V|$ vertices and $m=|E|$ arcs, which is *symmetric*: $(v,w)\in E$ if and only if $(w,v)\in E$. Each arc carries a real **capacity** $u(v,w)$ and a real **cost** $c(v,w)$, and the cost is *antisymmetric*: $c(v,w)=-c(w,v)$ for all $(v,w)\in E$. For a vertex $w$ write $E(w)=\{v \mid (w,v)\in E\}$.
--   2. A **circulation** is a real function $f$ on arcs with
--   $$
--   f(v,w)\le u(v,w),\qquad f(v,w)=-f(w,v)\quad\forall (v,w)\in E,\qquad \sum_{v\in E(w)} f(v,w)=0\quad\forall w\in V,
--   $$
--   the capacity, flow antisymmetry and conservation constraints (1)–(3).
--   3. The **cost** of $f$ is $\operatorname{cost}(f)=\tfrac12\sum_{(v,w)\in E}c(v,w)f(v,w)$, and $f$ is **minimum-cost** if it is a circulation and $\operatorname{cost}(f)\le\operatorname{cost}(g)$ for every circulation $g$.
--   4. The **residual capacity** of an arc is $u_f(v,w)=u(v,w)-f(v,w)$; an arc of $E$ with $u_f(v,w)>0$ is a **residual arc**. A **residual cycle** is a simple cycle all of whose arcs are residual arcs.
--   5. The **cost** of a cycle is the sum of the costs of its arcs, its **mean cost** is its cost divided by its number of arcs, and a **minimum-mean residual cycle** of $f$ is a residual cycle whose mean cost is at most that of every residual cycle of $f$.
--
--   These are the objects about which every statement of the mission is phrased.
--
--   **Formalization Note** Flows, capacities and costs are functions `V → V → ℝ`; their values off $E$ are never read. A cycle is a nonempty duplicate-free list $[v_0,\dots,v_{l-1}]$ of vertices; its arcs are $(v_0,v_1),\dots,(v_{l-2},v_{l-1}),(v_{l-1},v_0)$ and its length is $l$. One-vertex cycles (loops $(v,v)\in E$) and two-vertex cycles are allowed; by antisymmetry they have cost $0$, so they are never negative.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, pp. 875-876, Section 2, Eqs. (1)-(3) and the definitions of cost, residual arcs, residual cycles and mean cost

import Mathlib

namespace CycleCanceling.MinMean

/-- A circulation network (Goldberg–Tarjan 1989, §2, p. 875): a directed graph `G = (V, E)` on a
finite vertex type `V`, whose arc set `E` is symmetric (`(v, w) ∈ E ↔ (w, v) ∈ E`), with a real
capacity `u (v, w)` and a real cost `c (v, w)` on every arc; the cost is antisymmetric on `E`.
Values of `u` and `c` off `E` are never read. -/
structure CircNetwork (V : Type*) [Fintype V] [DecidableEq V] where
  /-- the arc set `E` -/
  E : Finset (V × V)
  /-- capacities `u (v, w)` -/
  u : V → V → ℝ
  /-- costs `c (v, w)` -/
  c : V → V → ℝ
  /-- `G` is symmetric -/
  symm : ∀ v w, (v, w) ∈ E ↔ (w, v) ∈ E
  /-- the cost is antisymmetric on `E` -/
  cost_antisymm : ∀ v w, (v, w) ∈ E → c v w = -c w v

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A circulation (§2, p. 876, constraints (1)–(3)): a real function `f` on arcs with
`f (v, w) ≤ u (v, w)` and `f (v, w) = -f (w, v)` for every `(v, w) ∈ E`, and
`∑_{v ∈ E(w)} f (v, w) = 0` for every vertex `w`, where `E(w) = {v | (w, v) ∈ E}`. -/
def IsCirculation (N : CircNetwork V) (f : V → V → ℝ) : Prop :=
  (∀ v w, (v, w) ∈ N.E → f v w ≤ N.u v w) ∧
  (∀ v w, (v, w) ∈ N.E → f v w = -f w v) ∧
  (∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), f v w = 0)

/-- `cost(f) = ½ ∑_{(v,w) ∈ E} c(v, w) f(v, w)` (§2, p. 876). -/
noncomputable def cost (N : CircNetwork V) (f : V → V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ a ∈ N.E, N.c a.1 a.2 * f a.1 a.2

/-- A minimum-cost circulation: a circulation whose cost is at most that of every circulation. -/
def IsMinCost (N : CircNetwork V) (f : V → V → ℝ) : Prop :=
  IsCirculation N f ∧ ∀ g, IsCirculation N g → cost N f ≤ cost N g

/-- Residual capacity `u_f(v, w) = u(v, w) - f(v, w)` (p. 876). -/
def resCap (N : CircNetwork V) (f : V → V → ℝ) (v w : V) : ℝ :=
  N.u v w - f v w

/-- The arcs of a cycle given by its vertex list `[v₀, v₁, …, v_{l-1}]`: the consecutive pairs
`(v₀, v₁), …, (v_{l-2}, v_{l-1}), (v_{l-1}, v₀)`. -/
def cycleArcs (Γ : List V) : List (V × V) :=
  Γ.zip (Γ.rotate 1)

/-- A residual cycle (p. 876): a simple cycle (nonempty, no repeated vertex) all of whose arcs are
residual arcs, i.e. arcs of `E` with positive residual capacity. -/
def IsResidualCycle (N : CircNetwork V) (f : V → V → ℝ) (Γ : List V) : Prop :=
  Γ ≠ [] ∧ Γ.Nodup ∧ ∀ a ∈ cycleArcs Γ, a ∈ N.E ∧ 0 < resCap N f a.1 a.2

/-- The cost of a cycle: the sum of the costs of its arcs (p. 876). -/
def cycleCost (N : CircNetwork V) (Γ : List V) : ℝ :=
  ((cycleArcs Γ).map (fun a => N.c a.1 a.2)).sum

/-- The mean cost of a cycle: its cost divided by its number of arcs `l = |Γ|` (p. 876). Only
applied to nonempty cycles. -/
noncomputable def meanCost (N : CircNetwork V) (Γ : List V) : ℝ :=
  cycleCost N Γ / (Γ.length : ℝ)

/-- `Γ` is a minimum-mean residual cycle of `f`: a residual cycle whose mean cost is at most the
mean cost of every residual cycle of `f`. -/
def IsMinMeanResidualCycle (N : CircNetwork V) (f : V → V → ℝ) (Γ : List V) : Prop :=
  IsResidualCycle N f Γ ∧ ∀ Γ', IsResidualCycle N f Γ' → meanCost N Γ ≤ meanCost N Γ'

end CycleCanceling.MinMean


