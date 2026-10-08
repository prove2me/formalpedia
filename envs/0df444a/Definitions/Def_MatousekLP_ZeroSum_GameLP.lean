-- Prove2me | Definitions.Def_MatousekLP_ZeroSum_GameLP
-- name    : MatousekLP_ZeroSum_GameLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T12:05:07.790579+00:00
-- url     : https://prove2.me/theorems/9922f4ae-2802-47b4-9ce9-b15b5abc350e
-- title:
--   The linear programs of the proof of the minimax theorem: the dual of (8.1), (8.2) and (8.4)
-- statement:
--   Let $M$ be a real $m \times n$ matrix and write $\mathbf 1$ for the all-ones vector. This file defines the feasibility and optimality predicates of three linear programs used in Section 8.1 of Matoušek–Gärtner.
--
--   1. The **dual of (8.1)** for a fixed vector $\mathbf x \in \mathbb R^m$ is the one-variable program
--   $$
--   \text{maximize } x_0 \quad\text{subject to}\quad M^T\mathbf x - \mathbf 1 x_0 \ge \mathbf 0 ;
--   $$
--   a real $x_0$ is feasible if $x_0 \le (M^T\mathbf x)_j$ for every $j$.
--   2. The linear program **(8.2)** in the variables $x_0, x_1, \dots, x_m$:
--   $$
--   \text{maximize } x_0 \quad\text{subject to}\quad M^T\mathbf x - \mathbf 1 x_0 \ge \mathbf 0,\quad \sum_{i=1}^m x_i = 1,\quad \mathbf x \ge \mathbf 0 .
--   $$
--   An **optimal solution** $(\tilde x_0, \tilde{\mathbf x})$ is a feasible point with $\tilde x_0 \ge x_0$ for every feasible point $(x_0, \mathbf x)$.
--   3. The linear program **(8.4)** in the variables $y_0, y_1, \dots, y_n$:
--   $$
--   \text{minimize } y_0 \quad\text{subject to}\quad M\mathbf y - \mathbf 1 y_0 \le \mathbf 0,\quad \sum_{j=1}^n y_j = 1,\quad \mathbf y \ge \mathbf 0 .
--   $$
--   An **optimal solution** $(\tilde y_0, \tilde{\mathbf y})$ is a feasible point with $\tilde y_0 \le y_0$ for every feasible point $(y_0, \mathbf y)$.
--
--   Program (8.2) computes a worst-case optimal mixed strategy of Alice and (8.4) one of Bob; the two programs are dual to each other.
--
--   **Formalization Note** Vectors are functions `Fin m → ℝ`, inequalities between vectors are pointwise, and $\mathbf 1 x_0$ is `x₀ • (fun _ => 1)`. Optimality is stated against every feasible point, so no real supremum or infimum over a possibly empty or unbounded feasible set is used.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 137 (§8.1, the dual of the linear program (8.1)), p. 138, Eq. (8.2) and Eq. (8.4)

import Mathlib

open Matrix

namespace MatousekLP.ZeroSum

/-- Feasibility for the dual of the linear program (8.1) (p. 137), for a fixed vector `x`:
the single variable `x₀` satisfies `Mᵀx − 𝟏x₀ ≥ 0`, i.e. `x₀ ≤ (Mᵀx)_j` for every `j`. -/
def DualLP81Feasible {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (x₀ : ℝ) :
    Prop :=
  0 ≤ Mᵀ *ᵥ x - x₀ • (fun _ => (1 : ℝ))

/-- Feasibility for the linear program (8.2) (p. 138) in the variables `x₀, x₁, …, xₘ`:
`Mᵀx − 𝟏x₀ ≥ 0`, `∑ᵢ xᵢ = 1`, `x ≥ 0`. -/
def LP82Feasible {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (x₀ : ℝ) (x : Fin m → ℝ) : Prop :=
  0 ≤ Mᵀ *ᵥ x - x₀ • (fun _ => (1 : ℝ)) ∧ ∑ i, x i = 1 ∧ 0 ≤ x

/-- An optimal solution `(x₀, x)` of (8.2) ("maximize `x₀`"): a feasible point whose
objective `x₀` is at least that of every feasible point. -/
def LP82Optimal {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (x₀ : ℝ) (x : Fin m → ℝ) : Prop :=
  LP82Feasible M x₀ x ∧ ∀ (x₀' : ℝ) (x' : Fin m → ℝ), LP82Feasible M x₀' x' → x₀' ≤ x₀

/-- Feasibility for the linear program (8.4) (p. 138) in the variables `y₀, y₁, …, yₙ`:
`My − 𝟏y₀ ≤ 0`, `∑ⱼ yⱼ = 1`, `y ≥ 0`. -/
def LP84Feasible {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (y₀ : ℝ) (y : Fin n → ℝ) : Prop :=
  M *ᵥ y - y₀ • (fun _ => (1 : ℝ)) ≤ 0 ∧ ∑ j, y j = 1 ∧ 0 ≤ y

/-- An optimal solution `(y₀, y)` of (8.4) ("minimize `y₀`"): a feasible point whose
objective `y₀` is at most that of every feasible point. -/
def LP84Optimal {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (y₀ : ℝ) (y : Fin n → ℝ) : Prop :=
  LP84Feasible M y₀ y ∧ ∀ (y₀' : ℝ) (y' : Fin n → ℝ), LP84Feasible M y₀' y' → y₀ ≤ y₀'

end MatousekLP.ZeroSum


