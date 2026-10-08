-- Prove2me | Definitions.Def_MatousekLP_Duality_PrimalDual
-- name    : MatousekLP_Duality_PrimalDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T11:04:17.757398+00:00
-- url     : https://prove2.me/theorems/1998ea35-5bf3-48bc-97b6-557169f07cd6
-- title:
--   The primal linear program (P), its dual (D), and the four cases of the duality theorem
-- statement:
--   Let $A$ be a real matrix with $m$ rows and $n$ columns, $b\in\mathbb{R}^m$ and $c\in\mathbb{R}^n$. Chapter 6 of Matoušek & Gärtner studies the pair of linear programs
--
--   $$\text{(P)}\quad \text{maximize } c^{T}x \ \text{ subject to } Ax\le b,\ x\ge 0, \qquad\qquad \text{(D)}\quad \text{minimize } b^{T}y \ \text{ subject to } A^{T}y\ge c,\ y\ge 0,$$
--
--   where all inequalities between vectors are componentwise. This module fixes the vocabulary.
--
--   1. A **feasible solution** of (P) is an $x\in\mathbb{R}^n$ with $Ax\le b$ and $x\ge 0$; a feasible solution of (D) is a $y\in\mathbb{R}^m$ with $A^{T}y\ge c$ and $y\ge 0$.
--   2. An **optimal solution** of (P) is a feasible $x^*$ with $c^{T}x\le c^{T}x^*$ for every feasible $x$; an optimal solution of the minimization (D) is a feasible $y^*$ with $b^{T}y^*\le b^{T}y$ for every feasible $y$.
--   3. (P) is **unbounded** if for every real $M$ some feasible $x$ has $c^{T}x>M$; (D) is **unbounded (from below)** if for every real $M$ some feasible $y$ has $b^{T}y<M$.
--   4. The **four cases** of the duality theorem: (1) neither (P) nor (D) is feasible; (2) (P) is unbounded and (D) is infeasible; (3) (P) is infeasible and (D) is unbounded; (4) both are feasible, both have an optimal solution, and $c^{T}x^*=b^{T}y^*$ for every optimal $x^*$ of (P) and every optimal $y^*$ of (D).
--
--   These notions are the language of weak duality (Proposition 6.1.1) and of the duality theorem of linear programming.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, so the book's indices $1,\dots,n$ are $0,\dots,n-1$. Optimality and unboundedness are stated against every feasible point; no supremum or infimum is taken. The book's case $k$ is `DualityCase A b c (k-1)`, indexed by `Fin 4`.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 82 (§6.1, the linear programs (P) and (D)), p. 83 (§6.1, Duality theorem of linear programming, cases 1–4), pp. 2–4 (§1.1, feasible/optimal solution, unbounded)

import Mathlib

namespace MatousekLP.Duality

/-!
# The primal–dual pair (P), (D) of Chapter 6

Matoušek & Gärtner, *Understanding and Using Linear Programming*, Springer 2007,
§6.1, p. 82: for a real `m × n` matrix `A`, `b ∈ ℝ^m`, `c ∈ ℝ^n`,

* (P) maximize `cᵀx` subject to `Ax ≤ b` and `x ≥ 0`;
* (D) minimize `bᵀy` subject to `Aᵀy ≥ c` and `y ≥ 0`.

Feasible and optimal solutions and unboundedness follow §1.1, pp. 2–4.
All inequalities between vectors are componentwise.  The book's indices
`1, …, n` are `0, …, n-1` here.
-/

open Matrix

variable {m n : ℕ}

/-- `x` is a feasible solution of (P): `Ax ≤ b` and `x ≥ 0`. -/
def IsPrimalFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x ≤ b ∧ 0 ≤ x

/-- `y` is a feasible solution of (D): `Aᵀy ≥ c` and `y ≥ 0`. -/
def IsDualFeasible (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  c ≤ Aᵀ *ᵥ y ∧ 0 ≤ y

/-- `x` is an optimal solution of (P): it is feasible and `cᵀx' ≤ cᵀx` for every feasible `x'`. -/
def IsPrimalOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  IsPrimalFeasible A b x ∧ ∀ x', IsPrimalFeasible A b x' → c ⬝ᵥ x' ≤ c ⬝ᵥ x

/-- `y` is an optimal solution of the minimization (D): it is feasible and `bᵀy ≤ bᵀy'` for every
feasible `y'`. -/
def IsDualOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) : Prop :=
  IsDualFeasible A c y ∧ ∀ y', IsDualFeasible A c y' → b ⬝ᵥ y ≤ b ⬝ᵥ y'

/-- (P) is **unbounded**: its objective attains arbitrarily large values on feasible solutions. -/
def PrimalUnbounded (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ M : ℝ, ∃ x, IsPrimalFeasible A b x ∧ M < c ⬝ᵥ x

/-- (D) is **unbounded (from below)**: its objective attains arbitrarily small values on feasible
solutions. -/
def DualUnbounded (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ M : ℝ, ∃ y, IsDualFeasible A c y ∧ b ⬝ᵥ y < M

/-- The four possibilities of the duality theorem (§6.1, p. 83); the book's case `k` is
index `k - 1` here.

* `0`: neither (P) nor (D) has a feasible solution;
* `1`: (P) is unbounded and (D) has no feasible solution;
* `2`: (P) has no feasible solution and (D) is unbounded;
* `3`: both (P) and (D) have a feasible solution; then both have an optimal solution, and
  `cᵀx* = bᵀy*` for every optimal solution `x*` of (P) and every optimal solution `y*` of (D). -/
def DualityCase (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Fin 4 → Prop
  | 0 => (¬ ∃ x, IsPrimalFeasible A b x) ∧ (¬ ∃ y, IsDualFeasible A c y)
  | 1 => PrimalUnbounded A b c ∧ (¬ ∃ y, IsDualFeasible A c y)
  | 2 => (¬ ∃ x, IsPrimalFeasible A b x) ∧ DualUnbounded A b c
  | 3 => (∃ x, IsPrimalFeasible A b x) ∧ (∃ y, IsDualFeasible A c y) ∧
      (∃ x, IsPrimalOptimal A b c x) ∧ (∃ y, IsDualOptimal A b c y) ∧
      ∀ x y, IsPrimalOptimal A b c x → IsDualOptimal A b c y → c ⬝ᵥ x = b ⬝ᵥ y

end MatousekLP.Duality


