-- Prove2me | Definitions.Def_ConstrNestedLogit_Space_KnapsackLP
-- name    : ConstrNestedLogit_Space_KnapsackLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:02:52.994925+00:00
-- url     : https://prove2.me/theorems/64e1556d-2af7-40d9-bad1-5b9c7da1ed9c
-- title:
--   Finite continuous knapsack relaxation
-- statement:
--   For finitely many products, let $w_j$ be the space used by product $j$, $a_j$ its objective coefficient, and $c$ the capacity. A vector $x$ is feasible for the continuous relaxation of the zero-one knapsack when
--
--   $$0\le x_j\le 1\quad(j\in N),\qquad \sum_{j\in N}w_jx_j\le c.$$
--
--   Its objective is $\sum_j a_jx_j$. An optimal vector is feasible and has objective at least that of every feasible vector. This general definition is reusable for the paper's parameterized knapsack and other finite knapsack problems.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 19, linear programming relaxation of (10)

import Mathlib

namespace ConstrNestedLogit.Space

/-- Feasible points of the continuous relaxation of a finite 0–1 knapsack. -/
def knapsackLPFeasible {n : ℕ} (w : Fin n → ℝ) (c : ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ (∑ j, w j * x j) ≤ c

/-- Linear objective of the continuous knapsack relaxation. -/
def knapsackLPObjective {n : ℕ} (a : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j, a j * x j

/-- An optimal point of the continuous knapsack relaxation. -/
def knapsackLPOptimal {n : ℕ} (w a : Fin n → ℝ) (c : ℝ) (x : Fin n → ℝ) : Prop :=
  knapsackLPFeasible w c x ∧
    ∀ y, knapsackLPFeasible w c y → knapsackLPObjective a y ≤ knapsackLPObjective a x

end ConstrNestedLogit.Space


