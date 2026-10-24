-- Prove2me | Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame
-- name    : ZeroSumLP_DantzigExt_MatrixGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T20:12:14.711934+00:00
-- url     : https://prove2.me/theorems/d82a8437-98ff-4c42-8bcb-8d3fc9c6c88a
-- title:
--   Min-max and max-min strategies (7)–(8) and the value of a matrix game
-- statement:
--   A **zero-sum game** is given by a real matrix $A$ whose rows $i$ are the pure strategies of the maximizing **row player** and whose columns $j$ are the pure strategies of the minimizing **column player**; the entry $a_{ij}$ is the payoff to the row player, equivalently the cost to the column player. Mixed strategies of the column and row player are the probability vectors
--   $$X=\{x\ge \mathbf 0,\ \mathbf 1^\top x=1\},\qquad Y=\{y\ge \mathbf 0,\ \mathbf 1^\top y=1\}.$$
--
--   1. A **min-max strategy** $x$ with **min-max value** $v$ is an optimal solution of the LP (7):
--   $$\text{minimize}_{x,v}\ v\quad\text{subject to}\quad Ax\le \mathbf 1 v,\quad x\in X .$$
--   That is, $(x,v)$ is feasible for (7) and $v\le v'$ for every feasible pair $(x',v')$.
--   2. A **max-min strategy** $y$ with **max-min value** $u$ is an optimal solution of the LP (8):
--   $$\text{maximize}_{y,u}\ u\quad\text{subject to}\quad y^\top A\ge u\mathbf 1^\top,\quad y\in Y .$$
--   3. A real number $v$ is a **value** of the game if some min-max strategy has min-max value $v$.
--
--   By the minimax theorem (Theorem 2 of the paper) the min-max and max-min values coincide and are the value of the game. These three predicates are the game-theoretic vocabulary of every statement of this mission.
--
--   **Formalization Note** The rows and columns are indexed by arbitrary finite types, so that block matrices such as Dantzig's game can be indexed by sums of index types. Optimality is stated against every feasible pair, with no supremum or infimum of a possibly empty or unbounded set.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, pp. 5–6, (4)–(8)

import Mathlib

namespace ZeroSumLP.DantzigExt

open Matrix

/-- (7), p. 6: `x` is a **min-max strategy** of the zero-sum game with payoff matrix `A`
(rows: the maximizing row player, columns: the minimizing column player) with **min-max value**
`v`: the pair `(x, v)` is feasible for (7) — `x ∈ X` (5) and `A x ≤ 1 v` — and minimizes `v`
among all feasible pairs. -/
def IsMinMaxStrategy {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ)
    (x : κ → ℝ) (v : ℝ) : Prop :=
  (0 ≤ x ∧ ∑ j, x j = 1 ∧ A *ᵥ x ≤ fun _ => v) ∧
    ∀ (x' : κ → ℝ) (v' : ℝ), (0 ≤ x' ∧ ∑ j, x' j = 1 ∧ A *ᵥ x' ≤ fun _ => v') → v ≤ v'

/-- (8), p. 6: `y` is a **max-min strategy** of the game `A` with **max-min value** `u`: the pair
`(y, u)` is feasible for (8) — `y ∈ Y` (4) and `yᵀ A ≥ u 1ᵀ` — and maximizes `u` among all
feasible pairs. -/
def IsMaxMinStrategy {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ)
    (y : ι → ℝ) (u : ℝ) : Prop :=
  (0 ≤ y ∧ ∑ i, y i = 1 ∧ (fun _ => u) ≤ y ᵥ* A) ∧
    ∀ (y' : ι → ℝ) (u' : ℝ), (0 ≤ y' ∧ ∑ i, y' i = 1 ∧ (fun _ => u') ≤ y' ᵥ* A) → u' ≤ u

/-- `v` is a (min-max) **value** of the game `A`: some min-max strategy has min-max value `v`,
i.e. `v` is the optimal value of (7). -/
def IsGameValue {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (v : ℝ) : Prop :=
  ∃ x : κ → ℝ, IsMinMaxStrategy A x v

end ZeroSumLP.DantzigExt


