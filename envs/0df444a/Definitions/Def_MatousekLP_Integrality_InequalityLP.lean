-- Prove2me | Definitions.Def_MatousekLP_Integrality_InequalityLP
-- name    : MatousekLP_Integrality_InequalityLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T10:16:54.366415+00:00
-- url     : https://prove2.me/theorems/9d4a1329-8c96-43b3-86ff-cf38eeff0581
-- title:
--   Feasible and optimal solutions of $\max c^T x$ s.t. $Ax \le b$, $x \ge 0$
-- statement:
--   Let $A$ be a real $m \times n$ matrix, $b \in \mathbb{R}^m$ and $c \in \mathbb{R}^n$, and consider the linear program
--   $$
--   \text{maximize } c^T x \quad \text{subject to } Ax \le b,\ x \ge 0 .
--   $$
--   A vector $x \in \mathbb{R}^n$ is **feasible** if $Ax \le b$ and $x \ge 0$ hold componentwise. It is an **optimal solution** if it is feasible and $c^T y \le c^T x$ for every feasible $y$.
--
--   This is the linear program of Lemma 8.2.4, whose integral optimal solutions are the subject of total unimodularity.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ` (the book's $x_1, \dots, x_n$ are $x_0, \dots, x_{n-1}$), inequalities between vectors are componentwise, and optimality is expressed against every feasible point rather than through a supremum, so no optimum value has to exist for the definition to make sense.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 145, Lemma 8.2.4 (the linear program maximize c^T x subject to Ax ≤ b, x ≥ 0)

import Mathlib

namespace MatousekLP.Integrality

/-- Feasibility for the linear program `maximize cᵀx subject to Ax ≤ b, x ≥ 0`
(Lemma 8.2.4, p. 145): `x` is feasible if `Ax ≤ b` componentwise and `x ≥ 0`. -/
def IsFeasibleIneq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  A.mulVec x ≤ b ∧ 0 ≤ x

/-- `x` is an optimal solution of `maximize cᵀx subject to Ax ≤ b, x ≥ 0`: it is feasible
and its objective value `cᵀx` is at least that of every feasible point. -/
def IsOptimalIneq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  IsFeasibleIneq A b x ∧
    ∀ y : Fin n → ℝ, IsFeasibleIneq A b y → dotProduct c y ≤ dotProduct c x

end MatousekLP.Integrality


