-- Prove2me | Definitions.Def_VanderbeiLP_Simplex_StandardForm
-- name    : VanderbeiLP_Simplex_StandardForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T16:50:31.575885+00:00
-- url     : https://prove2.me/theorems/3bdbc27d-6bff-40a3-9300-4cfae6373e1c
-- title:
--   Feasible, optimal, infeasible, unbounded and basic solutions of a standard-form LP
-- statement:
--   For the standard-form linear program
--   $$
--   \text{maximize } \zeta = \sum_{j=1}^n c_j x_j \quad\text{subject to}\quad \sum_{j=1}^n a_{ij}x_j \le b_i\ (i = 1,\dots,m),\qquad x_j \ge 0\ (j = 1,\dots,n),
--   $$
--   a **solution** is any $x \in \mathbb{R}^n$. It is **feasible** if it satisfies all the constraints, and **optimal** if in addition it attains the maximum of $\zeta$ over all feasible solutions. The problem is **infeasible** if it has no feasible solution, and **unbounded** if it has feasible solutions with arbitrarily large objective values: for every $M$ there is a feasible $x$ with $\sum_j c_jx_j > M$.
--
--   A solution $x$ is **basic** if the vector $(x_1,\dots,x_n,w_1,\dots,w_m)$ with slacks $w_i = b_i - \sum_j a_{ij}x_j$ is the basic solution of some dictionary (the solution obtained by setting its nonbasic variables to zero). A **basic feasible solution** is a feasible basic solution, and a **basic optimal solution** is an optimal basic solution.
--
--   These notions are the vocabulary of the fundamental theorem of linear programming.
--
--   **Formalization Note** "Basic" is defined through the dictionary structure of this mission, whose basic set carries $m$ linearly independent columns of $[A\ I]$; it is not a support condition.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, pp. 6–7 (PDF 25–26), standard form, feasible, optimal, infeasible, unbounded; p. 13 (PDF 31), basic feasible solutions; p. 14 (PDF 32), Eq. (2.5)

import Mathlib
import Definitions.Def_VanderbeiLP_Simplex_Dictionary

namespace VanderbeiLP.Simplex

variable {m n : ℕ}

/-- A solution `x` of the standard-form problem `maximize cᵀx s.t. Ax ≤ b, x ≥ 0`
(Vanderbei, pp. 6–7) is **feasible** if it satisfies all the constraints. -/
def IsFeasibleSol (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ i, ∑ j, A i j * x j ≤ b i) ∧ ∀ j, 0 ≤ x j

/-- The objective value `ζ = ∑_j c_j x_j`. -/
def objective (c : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j, c j * x j

/-- A solution is **optimal** if it is feasible and attains the maximum of the objective over
all feasible solutions. -/
def IsOptimalSol (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  IsFeasibleSol A b x ∧ ∀ y, IsFeasibleSol A b y → objective c y ≤ objective c x

/-- The problem is **infeasible** if it has no feasible solution. -/
def IsInfeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ∀ x, ¬ IsFeasibleSol A b x

/-- The problem is **unbounded** if it has feasible solutions with arbitrarily large objective
values. -/
def IsUnbounded (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ M : ℝ, ∃ x, IsFeasibleSol A b x ∧ M < objective c x

/-- The vector of all `n + m` variables `(x_1, …, x_n, w_1, …, w_m)` determined by `x`, with the
slacks `w_i = b_i − ∑_j a_{ij} x_j` (p. 14, (2.5)). -/
def withSlacks (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Fin (n + m) → ℝ :=
  Fin.append x (fun i => b i - ∑ j, A i j * x j)

/-- `x` is a **basic solution**: together with its slacks it is the solution of some dictionary
obtained by setting the nonbasic variables to zero (p. 13). -/
def IsBasicSol (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  ∃ D : Dictionary A, withSlacks A b x = D.bbar b

/-- A **basic feasible solution** (p. 13). -/
def IsBasicFeasibleSol (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Prop :=
  IsFeasibleSol A b x ∧ IsBasicSol A b x

/-- A **basic optimal solution**: an optimal solution that is basic. -/
def IsBasicOptimalSol (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  IsOptimalSol A b c x ∧ IsBasicSol A b x

end VanderbeiLP.Simplex


