-- Prove2me | Definitions.Def_StengelZeroSum_IsBasic
-- name    : StengelZeroSum_IsBasic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:53.751859+00:00
-- url     : https://prove2.me/theorems/8d832c10-8c89-41f4-9df6-2e251fb7994e
-- title:
--   Basic vectors: the columns in the support are linearly independent
-- statement:
--   For a real matrix $G$ and a vector $x$, $x$ is **basic** for $G$ if the columns $G_j$ of $G$ with $x_j\neq 0$ are linearly independent. A *basic solution* of $Gx=h$ is a solution that is basic; a *basic feasible solution* is moreover nonnegative.
--
--   This is the notion of the paper: "A basic solution $x$ to $Ax=b$ is given by a solution $x$ where the columns $A_j$ of $A$ with $x_j\neq0$ are linearly independent, which then determine uniquely the solution $x$."
--
--   **Formalization Note** Only the column condition is in the predicate; the equation $Gx=h$ and nonnegativity are stated separately where they are used. Rows and columns are arbitrary finite types.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, p.19

import Mathlib

namespace StengelZeroSum

/-- `x` is **basic** for the matrix `G`: the columns `G_j` of `G` with `x_j ≠ 0` are linearly
independent.
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, p.19:
"A basic solution x to Ax = b is given by a solution x where the columns A_j of A with x_j ≠ 0
are linearly independent, which then determine uniquely the solution x."

**Formalization Note** This predicate is only the column condition; a *basic solution* of
`Gx = h` is an `x` with `G *ᵥ x = h` and `IsBasic G x`, and a *basic feasible solution* adds
`0 ≤ x`. Rows and columns are arbitrary finite types. -/
def IsBasic {ρ κ : Type*} (G : Matrix ρ κ ℝ) (x : κ → ℝ) : Prop :=
  LinearIndependent ℝ (fun j : {j : κ // x j ≠ 0} => fun i => G i j)

end StengelZeroSum


