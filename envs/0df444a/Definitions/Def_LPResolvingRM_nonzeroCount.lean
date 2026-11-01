-- Prove2me | Definitions.Def_LPResolvingRM_nonzeroCount
-- name    : LPResolvingRM_nonzeroCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:39:17.861344+00:00
-- url     : https://prove2.me/theorems/91e14b3c-b631-4f0d-acf5-5cdba543e2fb
-- title:
--   Slack and nonzero count of the standard-form point $(y,\,b-Cy,\,\mathbf 1-y)$
-- statement:
--   For a matrix $A\in\mathbb R^{m\times n}$, a right-hand side $r\in\mathbb R^m$ and $y\in\mathbb R^n$, the *slack* is $s=r-Ay$, and the *nonzero count* of the standard-form point $(y,s,z)$ with $z=\mathbf 1-y$ is
--   $$|\{j:y_j\ne0\}|+|\{i:s_i\ne0\}|+|\{j:z_j\ne0\}|.$$
--
--   The LPs (6) and (8) of the paper are the standard form $\max w^\top y$ s.t. $Ay+s=r$, $y+z=\mathbf 1$, $y,s,z\ge0$ of the bounded LP $\max\{w^\top y: Ay\le r,\ 0\le y\le\mathbf 1\}$; their feasible points are exactly $(y,r-Ay,\mathbf 1-y)$ with $y$ feasible for the bounded LP, with the same objective. Assumption 2 counts the nonzero coordinates of this point.
--
--   **Formalization Note** Feasibility and optimality of the bounded LP are the published `LPAllocRM.LPFeasible` and `LPAllocRM.IsLPOptimal` with upper bound $u=\mathbf 1$; this item adds only the slack and the count.
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, (6), p.8; Assumption 2, p.9; (8), p.9

import Mathlib

open scoped Classical
open Matrix

namespace LPResolvingRM

/-- The **resource slack** `s = r − A y` of the standard form (6)/(8) of the resource-allocation
LP `max wᵀy s.t. Ay ≤ r, 0 ≤ y ≤ 1` (arXiv:2101.11092v3, p.8). -/
def slack {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ) (y : Fin n → ℝ) :
    Fin m → ℝ :=
  fun i => r i - (A *ᵥ y) i

/-- The number of **nonzero coordinates of the standard-form point** `(y, s, z)` with
`s = r − A y` and `z = 1 − y` (arXiv:2101.11092v3, Assumption 2, p.9):
`|{j : y_j ≠ 0}| + |{i : s_i ≠ 0}| + |{j : z_j ≠ 0}|`.

**Formalization Note.** The standard form `max wᵀy s.t. Ay + s = r, y + z = 1, y, s, z ≥ 0` of
the LPs (6) and (8) has exactly the feasible points `(y, r − Ay, 1 − y)` with `y` feasible for
`max wᵀy s.t. Ay ≤ r, 0 ≤ y ≤ 1` (the published `LPAllocRM.IsLPOptimal` with upper bound `1`),
with the same objective; so it is written through its `y`-part. -/
noncomputable def nonzeroCount {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (y : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter fun j => y j ≠ 0).card +
    (Finset.univ.filter fun i => slack A r y i ≠ 0).card +
    (Finset.univ.filter fun j => 1 - y j ≠ 0).card

end LPResolvingRM


