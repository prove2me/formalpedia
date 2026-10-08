-- Prove2me | Definitions.Def_BalasAdditive_Convergence_BinaryLP
-- name    : BalasAdditive_Convergence_BinaryLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:48:25.267087+00:00
-- url     : https://prove2.me/theorems/f3160a8e-807e-4b42-a67f-5802c1f33a9b
-- title:
--   Finite real zero-one linear minimization problem
-- statement:
--   A finite **zero-one linear program** has a real matrix $A=(a_{ij})$, a right-hand side $b=(b_i)$, and objective coefficients $c=(c_j)$. A binary assignment is identified with its set $J$ of coordinates equal to one. Its slack in row $i$ and its objective value are
--
--   $$y_i(J)=b_i-\sum_{j\in J}a_{ij},\qquad z(J)=\sum_{j\in J}c_j.$$
--
--   The assignment is feasible when every $y_i(J)\ge 0$. It is optimal when it is feasible and $z(J)\le z(K)$ for every feasible assignment $K$.
--
--   This general model provides the reusable binary-program object on which Balas's nonnegative-cost problem is built.
-- source:
--   Balas, An additive algorithm for solving linear programs with zero-one variables, Oper. Res. 13 (1965), pp. 519, 523, Eqs. (1)–(8), DOI 10.1287/opre.13.4.517

import Mathlib

set_option autoImplicit false

namespace BalasAdditive.Convergence

/-- A finite real zero-one minimization problem in inequality form. -/
structure BinaryLP (n m : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ

/-- The slack determined by the binary assignment represented by `J`. -/
def BinaryLP.slack {n m : ℕ} (P : BinaryLP n m) (J : Finset (Fin n)) (i : Fin m) : ℝ :=
  P.b i - ∑ j ∈ J, P.A i j

/-- The objective value of a binary assignment. -/
def BinaryLP.cost {n m : ℕ} (P : BinaryLP n m) (J : Finset (Fin n)) : ℝ :=
  ∑ j ∈ J, P.c j

/-- Binary assignments are feasible exactly when all slacks are nonnegative. -/
def BinaryLP.Feasible {n m : ℕ} (P : BinaryLP n m) (J : Finset (Fin n)) : Prop :=
  ∀ i, 0 ≤ P.slack J i

/-- An optimal binary assignment has no more costly feasible competitor. -/
def BinaryLP.Optimal {n m : ℕ} (P : BinaryLP n m) (J : Finset (Fin n)) : Prop :=
  P.Feasible J ∧ ∀ K, P.Feasible K → P.cost J ≤ P.cost K

end BalasAdditive.Convergence


