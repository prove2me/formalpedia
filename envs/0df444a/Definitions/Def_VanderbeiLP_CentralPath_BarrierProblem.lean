-- Prove2me | Definitions.Def_VanderbeiLP_CentralPath_BarrierProblem
-- name    : VanderbeiLP_CentralPath_BarrierProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T19:15:58.44635+00:00
-- url     : https://prove2.me/theorems/fb6d0c30-1f06-4532-902a-8300a6b15ff0
-- title:
--   The barrier problem $\max c^Tx + \mu\sum_j\log x_j + \mu\sum_i\log w_i$, $Ax+w=b$, and the central-path system (17.6)
-- statement:
--   Fix integers $m, n \ge 0$, a real $m \times n$ matrix $A = (a_{ij})$, a right-hand side $b \in \mathbb{R}^m$ and an objective vector $c \in \mathbb{R}^n$. Chapter 17 studies the linear program and its dual
--
--   $$\text{maximize } c^T x \ \text{ s.t. } Ax \le b,\ x \ge 0, \qquad\qquad \text{minimize } b^T y \ \text{ s.t. } A^T y \ge c,\ y \ge 0,$$
--
--   written with slack variables as in (17.1): $Ax + w = b$, $x, w \ge 0$ for the primal and $A^T y - z = c$, $y, z \ge 0$ for the dual. For a vector $\xi$, $\xi > 0$ means that every component is strictly positive. This file defines:
--
--   1. the **primal feasible set** $\{x \in \mathbb{R}^n : Ax \le b,\ x \ge 0\}$ and the **dual feasible set** $\{y \in \mathbb{R}^m : A^T y \ge c,\ y \ge 0\}$;
--   2. **the primal feasible region has nonempty interior**: there is a primal feasible point $(\bar x, \bar w)$ with $A\bar x + \bar w = b$, $\bar x > 0$ and $\bar w > 0$;
--   3. **the dual feasible region has nonempty interior**: there is a dual feasible point $(\bar y, \bar z)$ with $A^T\bar y - \bar z = c$, $\bar y > 0$ and $\bar z > 0$;
--   4. for a parameter $\mu$, the **logarithmic barrier function** (17.7)
--   $$f(x, w) = c^T x + \mu \sum_{j=1}^n \log x_j + \mu \sum_{i=1}^m \log w_i;$$
--   5. a **solution of the barrier problem** (17.2)
--   $$\text{maximize } c^T x + \mu \sum_j \log x_j + \mu \sum_i \log w_i \quad \text{subject to } Ax + w = b:$$
--   a pair $(x, w)$ with $Ax + w = b$, $x > 0$, $w > 0$ such that $f(x', w') \le f(x, w)$ for every $(x', w')$ with $Ax' + w' = b$, $x' > 0$, $w' > 0$;
--   6. a **solution of the primal–dual central-path system** (17.6)
--   $$Ax + w = b, \qquad A^T y - z = c, \qquad XZe = \mu e, \qquad YWe = \mu e,$$
--   that is, $x_j z_j = \mu$ for every $j$ and $y_i w_i = \mu$ for every $i$, with $x, w, y, z > 0$.
--
--   Here $X, Z, Y, W$ are the diagonal matrices with the entries of $x, z, y, w$ on the diagonal and $e$ is the vector of ones. These are the objects of Theorem 17.2 (existence of a barrier solution) and Corollary 17.3 (existence and uniqueness of the central path point for each $\mu > 0$).
--
--   **Formalization Note** "Nonempty interior" is not the topological interior in $\mathbb{R}^{n+m}$: the region $\{(x, w) : Ax + w = b,\ x, w \ge 0\}$ lies in an affine subspace, whose topological interior is empty as soon as $m \ge 1$. The book fixes the meaning in the proof of Theorem 17.2 (p. 265): a feasible point with all components strictly positive, which is what items 2 and 3 say. The barrier function is $-\infty$ on the boundary of the orthant in the book; Lean's `Real.log` returns $0$ at non-positive arguments, so the barrier problem is stated over the open domain $x > 0$, $w > 0$ explicitly and the barrier function is never evaluated outside it. The book derives (17.6) from the barrier problem, whose domain is $x > 0$, $w > 0$; Exercise 17.3 (p. 267) writes $x, y, z, w > 0$ with the same system, and the positivity is part of the solution set here. Vectors are functions `Fin n → ℝ`, `Fin m → ℝ`; $A$ is a `Matrix (Fin m) (Fin n) ℝ`.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 257 (primal and dual, PDF p. 267); p. 258, Eqs. (17.1)–(17.2) (PDF p. 268); p. 263, Eq. (17.6) (PDF p. 273); p. 264, Eq. (17.7) (PDF p. 274); p. 265, proof of Theorem 17.2 (meaning of nonempty interior, PDF p. 275)

import Mathlib

open Matrix

namespace VanderbeiLP.CentralPath

/-- The primal feasible set `{x : Ax ≤ b, x ≥ 0}` of the LP
`maximize cᵀx subject to Ax ≤ b, x ≥ 0` (Vanderbei, p. 257). -/
def primalFeasibleSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ ∀ i, (A *ᵥ x) i ≤ b i}

/-- The dual feasible set `{y : Aᵀy ≥ c, y ≥ 0}` of the dual LP
`minimize bᵀy subject to Aᵀy ≥ c, y ≥ 0` (Vanderbei, p. 257). -/
def dualFeasibleSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    Set (Fin m → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∀ j, c j ≤ (Aᵀ *ᵥ y) j}

/-- The primal feasible region `{(x, w) : Ax + w = b, x, w ≥ 0}` of (17.1) has nonempty
interior, in the sense fixed by the proof of Theorem 17.2 (p. 265): there is a primal feasible
point `(x̄, w̄)` with `x̄ > 0` and `w̄ > 0` (every component strictly positive). -/
def PrimalStrictlyFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ∃ (x : Fin n → ℝ) (w : Fin m → ℝ), A *ᵥ x + w = b ∧ (∀ j, 0 < x j) ∧ ∀ i, 0 < w i

/-- The dual feasible region `{(y, z) : Aᵀy − z = c, y, z ≥ 0}` of (17.1) has nonempty
interior, in the sense fixed by the proof of Theorem 17.2 (p. 265): there is a dual feasible
point `(ȳ, z̄)` with `ȳ > 0` and `z̄ > 0`. -/
def DualStrictlyFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) : Prop :=
  ∃ (y : Fin m → ℝ) (z : Fin n → ℝ), Aᵀ *ᵥ y - z = c ∧ (∀ i, 0 < y i) ∧ ∀ j, 0 < z j

/-- The logarithmic barrier function (17.7):
`f(x, w) = cᵀx + μ ∑ⱼ log xⱼ + μ ∑ᵢ log wᵢ`.
It is only meaningful for `x > 0`, `w > 0`; every use below restricts to that domain. -/
noncomputable def barrierFunction {m n : ℕ} (c : Fin n → ℝ) (μ : ℝ) (x : Fin n → ℝ)
    (w : Fin m → ℝ) : ℝ :=
  c ⬝ᵥ x + μ * ∑ j, Real.log (x j) + μ * ∑ i, Real.log (w i)

/-- `(x, w)` is a solution of the barrier problem (17.2)
`maximize cᵀx + μ ∑ⱼ log xⱼ + μ ∑ᵢ log wᵢ subject to Ax + w = b`:
it lies in the domain of the barrier (`Ax + w = b`, `x > 0`, `w > 0`) and maximizes the barrier
function (17.7) over that domain. -/
def IsBarrierSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (μ : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) : Prop :=
  A *ᵥ x + w = b ∧ (∀ j, 0 < x j) ∧ (∀ i, 0 < w i) ∧
    ∀ (x' : Fin n → ℝ) (w' : Fin m → ℝ), A *ᵥ x' + w' = b → (∀ j, 0 < x' j) →
      (∀ i, 0 < w' i) → barrierFunction c μ x' w' ≤ barrierFunction c μ x w

/-- `(x, w, y, z)` solves the primal–dual central-path system (17.6)
`Ax + w = b, Aᵀy − z = c, XZe = μe, YWe = μe`, with `x, w, y, z > 0`
(the domain of the barrier problem, from which (17.6) is derived on p. 263). -/
def IsCentralPathPoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (μ : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) (y : Fin m → ℝ)
    (z : Fin n → ℝ) : Prop :=
  A *ᵥ x + w = b ∧ Aᵀ *ᵥ y - z = c ∧ (∀ j, x j * z j = μ) ∧ (∀ i, y i * w i = μ) ∧
    (∀ j, 0 < x j) ∧ (∀ i, 0 < w i) ∧ (∀ i, 0 < y i) ∧ ∀ j, 0 < z j

end VanderbeiLP.CentralPath


