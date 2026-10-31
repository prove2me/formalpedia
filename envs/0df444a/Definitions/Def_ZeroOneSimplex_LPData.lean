-- Prove2me | Definitions.Def_ZeroOneSimplex_LPData
-- name    : ZeroOneSimplex_LPData
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:19.549932+00:00
-- url     : https://prove2.me/theorems/56cdd74b-b0c2-40db-bb84-cb16d8617b3e
-- title:
--   The LP of form (1), its feasible region, and 0/1-LPs
-- statement:
--   An LP of **form (1)** has $n$ variables, $m$ equalities and $p$ further inequalities:
--   $$
--   \max\{c^\top x : Ax = b,\ Dx \le d,\ x \ge 0\},
--   $$
--   with $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $D\in\mathbb R^{p\times n}$, $d\in\mathbb R^p$ and an objective $c\in\mathbb R^n$. Its **feasible region** is $P=\{x\in\mathbb R^n : Ax=b,\ Dx\le d,\ x\ge 0\}$.
--
--   The LP is a **0/1-LP** when $c\in\mathbb Z^n$ and $P$ is a polytope (nonempty and bounded) all of whose extreme points lie in $\{0,1\}^n$. Nothing is assumed about the values of slack variables at vertices.
--
--   The dimension $d=\dim P$ used by the mission's theorems is the dimension of the affine hull of $P$, i.e. $\dim \operatorname{span}(P-P)$.
--
--   **Formalization Note** The paper lists $x\ge 0$ among the inequalities $Dx\le d$ (assumption (ii), p.6); here $x\ge 0$ is kept apart and $D$ holds only the other inequalities. All data are real, because §3.4 treats a general LP whose objective may be a random perturbation (p.25). Integrality of $c$ is a clause of the 0/1-LP predicate, the only place it is used; integrality of $A,b,D,d$ is never used. Full row rank of $A$ (assumption (i)) is a hypothesis of the theorems that need it.
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, display (1), p.2; §1.1, p.6 (assumptions (i), (ii)); p.1 (0/1 polytopes)

import Mathlib

set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

/-- **The LP of form (1).** Black, De Loera, Kafer, Sanità, *On the Simplex method for 0/1
polytopes*, arXiv:2111.14050v1, display (1), p.2, and §1.1, p.6:
`max { cᵀx : Ax = b, Dx ≤ d, x ∈ ℝⁿ }`, where the inequalities contain `x ≥ 0`
(assumption (ii), p.6).

The data are `n` variables, `m` equalities `A x = b` and `p` further inequalities `D x ≤ d`.

**Formalization Note.** The inequalities `x ≥ 0`, which assumption (ii) places among
`Dx ≤ d`, are kept apart: `D` holds only the other `p` inequalities, and the feasible region is
`{x | Ax = b, Dx ≤ d, x ≥ 0}` (`feasibleRegion`). All data are real: §3.4 (pp.22–25) treats a
general LP whose objective may be a random perturbation (p.25), so `c ∈ ℝⁿ` here, and integrality
of `c` is a clause of `IsZeroOneLP`, the only place it is used. The paper's integrality of
`A, b, D, d` is never used. -/
structure LPData (n m p : ℕ) where
  /-- the equality matrix `A ∈ ℝ^{m×n}` -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- the right-hand side `b ∈ ℝ^m` -/
  b : Fin m → ℝ
  /-- the inequality matrix `D ∈ ℝ^{p×n}` (inequalities other than `x ≥ 0`) -/
  D : Matrix (Fin p) (Fin n) ℝ
  /-- the right-hand side `d ∈ ℝ^p` -/
  d : Fin p → ℝ
  /-- the objective `c ∈ ℝⁿ` -/
  c : Fin n → ℝ

namespace LPData

variable {n m p : ℕ} (L : LPData n m p)

/-- The feasible region `P = {x ∈ ℝⁿ : Ax = b, Dx ≤ d, x ≥ 0}` of the LP (1)
(arXiv:2111.14050v1, p.6). -/
def feasibleRegion : Set (Fin n → ℝ) :=
  {x | L.A *ᵥ x = L.b ∧ L.D *ᵥ x ≤ L.d ∧ 0 ≤ x}

/-- **0/1-LP of the form (1)** (arXiv:2111.14050v1, pp.1–2, 6): the feasible region `P` is a
polytope (nonempty and bounded) all of whose extreme points lie in `{0,1}ⁿ`, and the objective
`c` is integral. Nothing is assumed about the slack values at vertices (p.6). -/
def IsZeroOneLP : Prop :=
  L.feasibleRegion.Nonempty ∧ Bornology.IsBounded L.feasibleRegion ∧
    (∀ x ∈ Set.extremePoints ℝ L.feasibleRegion, ∀ i, x i = 0 ∨ x i = 1) ∧
      ∀ i, ∃ z : ℤ, L.c i = z

end LPData

end ZeroOneSimplex


