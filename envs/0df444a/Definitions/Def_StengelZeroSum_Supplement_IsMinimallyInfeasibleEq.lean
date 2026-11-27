-- Prove2me | Definitions.Def_StengelZeroSum_Supplement_IsMinimallyInfeasibleEq
-- name    : StengelZeroSum_Supplement_IsMinimallyInfeasibleEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:26:07.410618+00:00
-- url     : https://prove2.me/theorems/5f1ce58d-cae5-548a-875c-56ea7fcd69a3
-- title:
--   Minimally infeasible system of equations $Ax=b$
-- statement:
--   Let $A$ be a real $m\times n$ matrix with rows $a_1,\dots,a_m$ and let $b\in\mathbb R^m$. A set of linear equations is **infeasible** if it has no solution, and **minimally infeasible** if omitting any one equation makes it feasible. For the system $Ax=b$ of the $m$ equations $a_kx=b_k$ this means:
--
--   1. there is no $x\in\mathbb R^n$ with $Ax=b$, and
--   2. for every $i\in[m]$ there is $x\in\mathbb R^n$ with $a_kx=b_k$ for all $k\neq i$.
--
--   Theorem 10 of Conforti, Di Summa and Zambelli shows that a minimally infeasible system of inequalities $Ax\le b$ has minimally infeasible equations $Ax=b$.
--
--   **Formalization Note** Rows are indexed by $\mathrm{Fin}\,m$. The inequality version is the published `MatousekLP.Duality.IsMinimallyInfeasible`.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Section 10, p.26 (definition of minimally infeasible)

import Mathlib

open Matrix

namespace StengelZeroSum.Supplement

/-- The system of equations `Ax = b` is **minimally infeasible**, von Stengel, *Zero-Sum Games
and Linear Programming Duality*, arXiv:2205.11196v6, Section 10, p.26: "A set of linear
equations and inequalities is called infeasible if it has no solution, and minimally infeasible
if omitting any one equation or inequality makes it feasible." Here the set consists of the `m`
equations `a_k x = b_k`, one per row `a_k` of `A`: there is no `x` with `Ax = b`, and for every
`i` some `x` satisfies all equations except possibly the `i`th.

**Formalization Note** Rows are `Fin m`. The inequality version (`Ax ≤ b` minimally
infeasible) is the published `MatousekLP.Duality.IsMinimallyInfeasible`. -/
def IsMinimallyInfeasibleEq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  (¬ ∃ x : Fin n → ℝ, A *ᵥ x = b) ∧
    ∀ i : Fin m, ∃ x : Fin n → ℝ, ∀ k : Fin m, k ≠ i → (A *ᵥ x) k = b k

end StengelZeroSum.Supplement


