-- Prove2me | Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair
-- name    : VanderbeiLP_StrictComp_PrimalDualPair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T17:10:33.009399+00:00
-- url     : https://prove2.me/theorems/a4973891-8cc4-40e0-bd91-b875c19f80da
-- title:
--   The primal–dual pair $\max c^Tx,\ Ax+w=b$ / $\min b^Ty,\ A^Ty-z=c$: slacks, feasibility, optimality
-- statement:
--   Fix integers $m, n \ge 0$, an $m \times n$ real matrix $A = (a_{ij})$, a right-hand side $b \in \mathbb{R}^m$ and an objective vector $c \in \mathbb{R}^n$. The **primal** linear program in standard form is
--
--   $$\text{maximize } \sum_{j=1}^n c_j x_j \quad \text{subject to } \sum_{j=1}^n a_{ij} x_j \le b_i \ (i = 1,\dots,m), \quad x_j \ge 0 \ (j = 1,\dots,n),$$
--
--   and its **dual** is
--
--   $$\text{minimize } \sum_{i=1}^m b_i y_i \quad \text{subject to } \sum_{i=1}^m y_i a_{ij} \ge c_j \ (j = 1,\dots,n), \quad y_i \ge 0 \ (i = 1,\dots,m).$$
--
--   This file defines the objects every statement of the mission is phrased in:
--
--   1. the **primal slack** $w = b - Ax \in \mathbb{R}^m$, so that the primal reads $Ax + w = b$, $x, w \ge 0$;
--   2. the **dual slack** $z = A^T y - c \in \mathbb{R}^n$ (a left-hand side minus the corresponding right-hand side), so that the dual reads $A^T y - z = c$, $y, z \ge 0$;
--   3. **primal feasibility** of $x$: $x \ge 0$ and $w = b - Ax \ge 0$;
--   4. **dual feasibility** of $y$: $y \ge 0$ and $z = A^T y - c \ge 0$;
--   5. **primal optimality** of $x$: $x$ is primal feasible and $c^T x' \le c^T x$ for every primal feasible $x'$;
--   6. **dual optimality** of $y$: $y$ is dual feasible and $b^T y \le b^T y'$ for every dual feasible $y'$.
--
--   All inequalities between vectors are componentwise.
--
--   These are the standard-form problem (5.1), its dual, and their slack forms (10.9)–(10.10). Weak and strong duality, complementary slackness and strict complementarity are all statements about these six objects.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, `Fin m → ℝ` and $A$ is a `Matrix (Fin m) (Fin n) ℝ`. The slacks are functions of $x$ (resp. $y$), not free variables, so a "solution $(x, w)$" of the book is the vector $x$ together with the slack it determines. Optimality is attainment of the maximum (minimum) over the feasible set, as defined on p. 7; no value function or supremum is involved.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, pp. 54–55, Eq. (5.1) and its dual (PDF pp. 70–71); p. 57 (dual slack, PDF p. 73); p. 147, Eqs. (10.9)–(10.10) (PDF p. 160); p. 7 (feasible/optimal, PDF p. 26)

import Mathlib

open Matrix

namespace VanderbeiLP.StrictComp

/-- Primal slack vector `w = b - A x` of the standard-form LP (5.1)/(10.9):
`maximize cᵀx subject to Ax + w = b, x, w ≥ 0`. -/
def primalSlack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Fin m → ℝ :=
  b - A *ᵥ x

/-- Dual slack vector `z = Aᵀ y - c` of the dual (10.10):
`minimize bᵀy subject to Aᵀy - z = c, y, z ≥ 0`
(each dual slack is a left-hand side minus the corresponding right-hand side, p. 57). -/
def dualSlack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ) :
    Fin n → ℝ :=
  Aᵀ *ᵥ y - c

/-- `x` is feasible for the primal (5.1): `x ≥ 0` and `w = b - Ax ≥ 0`. -/
def PrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ i, 0 ≤ primalSlack A b x i

/-- `y` is feasible for the dual of (5.1): `y ≥ 0` and `z = Aᵀy - c ≥ 0`. -/
def DualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ) :
    Prop :=
  (∀ i, 0 ≤ y i) ∧ ∀ j, 0 ≤ dualSlack A c y j

/-- `x` is optimal for the primal: it is feasible and attains the maximum of `cᵀx`
over all primal feasible points (p. 7). -/
def PrimalOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  PrimalFeasible A b x ∧ ∀ x' : Fin n → ℝ, PrimalFeasible A b x' → c ⬝ᵥ x' ≤ c ⬝ᵥ x

/-- `y` is optimal for the dual: it is dual feasible and attains the minimum of `bᵀy`
over all dual feasible points. -/
def DualOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) : Prop :=
  DualFeasible A c y ∧ ∀ y' : Fin m → ℝ, DualFeasible A c y' → b ⬝ᵥ y ≤ b ⬝ᵥ y'

end VanderbeiLP.StrictComp


