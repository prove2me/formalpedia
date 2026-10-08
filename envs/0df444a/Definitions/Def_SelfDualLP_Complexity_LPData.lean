-- Prove2me | Definitions.Def_SelfDualLP_Complexity_LPData
-- name    : SelfDualLP_Complexity_LPData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:46.207387+00:00
-- url     : https://prove2.me/theorems/91ed5417-9e71-4272-bab1-c3db0b715295
-- title:
--   Standard-form (LP) and its dual (LD): feasibility and optimal solutions
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $c\in\mathbb R^n$. The paper's primal and dual linear programs are
--   $$
--   \text{(LP)}\quad \min\{c^Tx : Ax=b,\ x\ge 0\},\qquad
--   \text{(LD)}\quad \max\{b^Ty : A^Ty\le c\},
--   $$
--   with dual slacks $s=c-A^Ty\in\mathbb R^n$.
--
--   1. $x$ is **feasible** for (LP) if $Ax=b$ and $x\ge0$; (LP) is **feasible** if such an $x$ exists.
--   2. $x$ is an **optimal solution** of (LP) if it is feasible and $c^Tx\le c^Tx'$ for every feasible $x'$; (LP) **has a solution** if it has an optimal solution.
--   3. $(y,s)$ is **feasible** for (LD) if $A^Ty\le c$ and $s=c-A^Ty$; (LD) is **feasible** if some $y$ has $A^Ty\le c$.
--   4. $(y,s)$ is an **optimal solution** of (LD) if $y$ maximizes $b^Ty$ over $\{y: A^Ty\le c\}$ and $s=c-A^Ty$.
--
--   These are the conclusions Theorem 3 and Corollary 7 draw about (LP) and (LD).
--
--   **Formalization Note** The predicates are built on the published general-form LP definitions `LinearOptimization.stdFormLP`, `IsLpOptimal`, `dualFeasibleStd` and `IsLpDualOptimal`. The paper's phrase "(LP) has a solution (feasible and bounded)" is read as "(LP) has an optimal solution"; for linear programs the two are equivalent, but that equivalence is a theorem and is not built in.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 53, §1, (LP), (LD) and dual slacks; DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_LinearOptimization_DualLP

open Matrix

namespace SelfDualLP.Complexity

/-! The standard-form linear program (LP) `minimize cᵀx subject to Ax = b, x ≥ 0` and its dual
(LD) `maximize bᵀy subject to Aᵀy ≤ c`, with dual slacks `s = c − Aᵀy`
(Ye–Todd–Mizuno 1994, §1, p. 53), built on the published general-form LP
`LinearOptimization.stdFormLP` and its standard-form dual feasible set
`LinearOptimization.dualFeasibleStd`. The data `A ∈ ℝ^{m×n}`, `b ∈ ℝ^m`, `c ∈ ℝ^n` are real. -/

/-- `x` is feasible for (LP): `Ax = b` and `x ≥ 0`. -/
def LPFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  x ∈ LinearOptimization.generalFeasibleSet (LinearOptimization.stdFormLP A b c)

/-- (LP) is feasible: its constraints are consistent. -/
def LPIsFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Prop :=
  ∃ x, LPFeasible A b c x

/-- `x` is an optimal solution of (LP): it is feasible and `cᵀx ≤ cᵀx'` for every feasible `x'`. -/
def LPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  LinearOptimization.IsLpOptimal c
    (LinearOptimization.generalFeasibleSet (LinearOptimization.stdFormLP A b c)) x

/-- (LP) has a solution: it has an optimal solution. -/
def LPHasSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Prop :=
  ∃ x, LPOptimal A b c x

/-- `(y, s)` is feasible for (LD): `Aᵀy ≤ c` and `s = c − Aᵀy` is its dual slack. -/
def LDFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ)
    (s : Fin n → ℝ) : Prop :=
  y ∈ LinearOptimization.dualFeasibleStd A c ∧ s = c - Aᵀ *ᵥ y

/-- (LD) is feasible: some `y` has `Aᵀy ≤ c`. -/
def LDIsFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) : Prop :=
  (LinearOptimization.dualFeasibleStd A c).Nonempty

/-- `(y, s)` is an optimal solution of (LD): `y` maximizes `bᵀy` over `{y : Aᵀy ≤ c}` and
`s = c − Aᵀy` is its dual slack. -/
def LDOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  LinearOptimization.IsLpDualOptimal b (LinearOptimization.dualFeasibleStd A c) y ∧
    s = c - Aᵀ *ᵥ y

end SelfDualLP.Complexity


