-- Prove2me | Definitions.Def_MatousekLP_Integrality_PerfectMatchingLP
-- name    : MatousekLP_Integrality_PerfectMatchingLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T10:17:05.902832+00:00
-- url     : https://prove2.me/theorems/dd3306fd-a67b-44ac-ac3d-08b59f42e93b
-- title:
--   The perfect-matching integer program (3.1) and its LP relaxation
-- statement:
--   Let $G = (V, E)$ be a finite simple graph with real edge weights $w_e$, $e \in E$. The integer program (3.1) is
--   $$
--   \text{maximize } \sum_{e \in E} w_e x_e \quad \text{subject to } \sum_{e \in E:\, v \in e} x_e = 1 \text{ for each } v \in V, \quad x_e \in \{0,1\} \text{ for each } e \in E,
--   $$
--   and its **LP relaxation** replaces $x_e \in \{0,1\}$ by $0 \le x_e \le 1$. This item defines
--
--   1. feasibility for the LP relaxation: $0 \le x_e \le 1$ for all $e$ and $\sum_{e \ni v} x_e = 1$ for all $v$;
--   2. feasibility for the integer program (3.1): feasibility for the relaxation together with $x_e \in \{0, 1\}$ for all $e$;
--   3. the objective $w(x) = \sum_{e \in E} w_e x_e$.
--
--   A 0/1 feasible vector is exactly the indicator vector of a perfect matching, so (3.1) is the maximum-weight perfect matching problem.
--
--   **Formalization Note** Vectors are indexed by the edge set of $G$ (a finite subtype of `Sym2 V`).
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 33, integer program (3.1) and its LP relaxation

import Mathlib

namespace MatousekLP.Integrality

/-- Feasibility for the LP relaxation of the perfect-matching integer program (3.1)
(p. 33): a vector `x = (x_e)_{e ∈ E}` indexed by the edges of `G` with
`0 ≤ x_e ≤ 1` for every edge and `∑_{e ∈ E : v ∈ e} x_e = 1` for every vertex `v`. -/
def IsPMRelaxFeasible {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : G.edgeSet → ℝ) : Prop :=
  (∀ e, 0 ≤ x e ∧ x e ≤ 1) ∧
    ∀ v : V, (∑ e ∈ Finset.univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V)), x e) = 1

/-- Feasibility for the integer program (3.1) itself: feasible for the relaxation and
`x_e ∈ {0, 1}` for every edge. -/
def IsPMIntFeasible {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : G.edgeSet → ℝ) : Prop :=
  IsPMRelaxFeasible G x ∧ ∀ e, x e = 0 ∨ x e = 1

/-- The objective `∑_{e ∈ E} w_e x_e` of (3.1) and of its LP relaxation. -/
def pmObjective {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w x : G.edgeSet → ℝ) : ℝ :=
  ∑ e, w e * x e

end MatousekLP.Integrality


