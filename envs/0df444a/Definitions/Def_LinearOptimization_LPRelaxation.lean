-- Prove2me | Definitions.Def_LinearOptimization_LPRelaxation
-- name    : LinearOptimization_LPRelaxation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-09T15:59:04.185411+00:00
-- url     : https://prove2.me/theorems/dbcd2390-b333-427c-b2fe-b0578b153888
-- title:
--   Linear programming relaxation
-- statement:
--   **(Definition 10.1, Bertsimas & Tsitsiklis, p. 462.)** Given a mixed integer programming problem
--
--   $$\begin{aligned}\text{minimize}\quad & c'x + d'y\\ \text{subject to}\quad & Ax + By = b\\ & x, y \ge 0\\ & x\ \text{integer},\end{aligned}$$
--
--   its *linear programming relaxation* is defined as
--
--   $$\begin{aligned}\text{minimize}\quad & c'x + d'y\\ \text{subject to}\quad & Ax + By = b\\ & x, y \ge 0,\end{aligned}$$
--
--   where the requirement that $x$ is a vector of integers was relaxed. If the integer variables $x_i$ are further restricted to be either $0$ or $1$, then in the linear programming relaxation $x_i$ takes values between $0$ and $1$.
--
--   (In Section 11.4 the relevant instance is the relaxation $Z_{LP} = \min\{c'x : Ax \ge b,\ Dx \ge d\}$ of problem (11.5), p. 498.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Definition 10.1, p. 462; Section 11.4 instance p. 498

import Definitions.Def_LinearOptimization_IntegerProgram

/-!
Linear programming relaxations of (mixed) integer programs.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997:

- **Definition 10.1 (p. 462).** The *linear programming relaxation* of the
  mixed integer program `min c'x + d'y, Ax + By = b, x, y ≥ 0, x integer`
  is the same problem with the integrality requirement on `x` dropped.
  (When the integer variables were `0`–`1` variables encoded with the box
  constraints `0 ≤ xᵢ ≤ 1`, the relaxed `xᵢ` ranges over `[0, 1]` — the
  box rows stay in the constraint data.)
- **§11.4 instance (p. 498).** For the inequality-form integer program
  (11.5), the relevant relaxation is
  `Z_LP = min {c'x | Ax ≥ b, Dx ≥ d}`.

Both relaxed values are `EReal`-valued via Mission I's `lpValue`.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Definition 10.1 (p. 462).** The feasible set of the linear
programming relaxation of the equality-form mixed integer program: the
integrality clause of `mixedIntegerFeasibleSet` is dropped, leaving the
standard-form polyhedron `{x | Ax = b, x ≥ 0}`. -/
def lpRelaxationSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  stdPolyhedron A b

/-- The relaxation contains the mixed-integer feasible set (dropping a
constraint enlarges the feasible set) — the source of the bound
`Z_LP ≤ Z_MIP`. -/
theorem mixedIntegerFeasibleSet_subset_lpRelaxationSet {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (I : Set (Fin n)) :
    mixedIntegerFeasibleSet A b I ⊆ lpRelaxationSet A b :=
  fun _ hx => hx.1

/-- **Bertsimas & Tsitsiklis, §11.4 (p. 498).** `Z_LP`, the optimal cost of the linear
programming relaxation `min {c'x | Ax ≥ b, Dx ≥ d}` of problem (11.5),
`EReal`-valued. -/
noncomputable def lpRelaxationValue {m₁ m₂ n : ℕ} (c : Fin n → ℝ)
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (D : Matrix (Fin m₂) (Fin n) ℝ) (d : Fin m₂ → ℝ) : EReal :=
  lpValue c (polyhedron A b ∩ polyhedron D d)

end LinearOptimization


