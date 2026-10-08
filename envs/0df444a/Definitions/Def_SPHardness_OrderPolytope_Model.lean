-- Prove2me | Definitions.Def_SPHardness_OrderPolytope_Model
-- name    : SPHardness_OrderPolytope_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:19.359618+00:00
-- url     : https://prove2.me/theorems/2c009758-2863-4d8b-8e5e-c088a002fd81
-- title:
--   §3, p. 11 — problem (10) and its expected recourse under the uniform cube law
-- statement:
--   Let $P$ be a finite partially ordered set with $k=|P|$, and let $C=[0,1]^P$ be its unit cube. For a realization $\xi\in\mathbb R^P$, the **second-stage program (10)** maximizes $z$ over $0\le z\le1$ and nonnegative $y_{ij}$, subject to
--
--   $$
--   z\le\sum_{i,j\in P:\,i\le_P j}(\xi_i-\xi_j)y_{ij}.
--   $$
--
--   Its optimal value is $q_P(\xi)$, and its **expected recourse value** is $Q(P)=\int_C q_P(\xi)\,d\xi$. This model is the stochastic-programming object used in Theorem 3.
--
--   **Formalization Note** The cube is imported from the separate order-polytope definition. The integral uses Lebesgue measure restricted to $C$, whose total mass is one. The value is the real supremum of feasible $z$; the feasible set contains zero and is bounded above by one, so no default value of real `sSup` is used. The finite sum includes reflexive pairs $i=j$, each contributing zero. The order comparison in that sum uses classical decidability.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 11, second-stage problem (10) and its expected value. https://optimization-online.org/wp-content/uploads/2015/03/4825.pdf

import Mathlib
import Definitions.Def_SPHardness_OrderPolytope_Core

namespace SPHardness.OrderPolytope

open MeasureTheory

/-- Feasible objective levels of the random-recourse linear program (10). -/
noncomputable def secondStageFeasible (P : Type) [Fintype P] [PartialOrder P]
    (ξ : P → ℝ) (z : ℝ) : Prop := by
  classical
  exact ∃ y : P → P → ℝ,
    (∀ i j : P, 0 ≤ y i j) ∧ 0 ≤ z ∧ z ≤ 1 ∧
    z ≤ ∑ i : P, ∑ j : P, if i ≤ j then (ξ i - ξ j) * y i j else 0

/-- Optimal value of the random-recourse linear program (10). -/
noncomputable def secondStageValue (P : Type) [Fintype P] [PartialOrder P]
    (ξ : P → ℝ) : ℝ :=
  sSup {z : ℝ | secondStageFeasible P ξ z}

/-- Expected value of (10) under the uniform law on the unit cube. -/
noncomputable def expRecourse (P : Type) [Fintype P] [PartialOrder P] : ℝ :=
  ∫ ξ in cube P, secondStageValue P ξ

end SPHardness.OrderPolytope


