-- Prove2me | Definitions.Def_FairFlows_CoverLP
-- name    : FairFlows_CoverLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:54.591194+00:00
-- url     : https://prove2.me/theorems/d5b7c27b-7ac8-4652-9bc8-987bb5d937da
-- title:
--   The linear programs (3.2), (3.3) and total dual integrality of $[A_Lx_L\ge p,\ x_L\le 1,\ x_L\ge 0]$
-- statement:
--   Let $D_L=(V,L)$ and $p:2^V\to\mathbb Z\cup\{-\infty\}$. $A_L$ is the $(0,1)$-matrix whose rows are the sets $X\subseteq V$ with $p(X)>-\infty$ and whose columns are the edges of $L$, the entry at $(X,e)$ being $1$ if $e$ enters $X$.
--
--   1. For a cost vector $c$, a vector $x\in\mathbb R^L$ is **primal feasible** if $A_Lx\ge p$ and $0\le x\le 1$, and **primal optimal** if moreover it minimizes $cx$ among feasible vectors; for $c=\mathbf 1$ this is (3.2).
--   2. A pair $(y,z)$, $y$ on the rows and $z$ on $L$, is **dual feasible** if $yA_L-z\le c$ and $(y,z)\ge0$, and **dual optimal** if it maximizes $yp-\mathbf 1z$; for $c=\mathbf 1$ this is (3.3).
--   3. The system $[A_Lx_L\ge p,\ x_L\le 1,\ x_L\ge 0]$ is **totally dual integral** (TDI) if for every integral $c$ for which the optimum is finite the dual has an integral optimal solution.
--   4. The **support family** of $y$ is $\{Z: y(Z)>0\}$, and a real vector is **integer-valued** if all its entries are integers.
--
--   These are the objects of Theorem 3.1 and Claim 3.3.
--
--   **Formalization Note** TDI is the published `BoxTDIMinMax.Separable.IsTDI` (an integral optimal dual whenever $\max\{yb: y\ge0,\ yM=c\}$ is finite) applied to $M=[A_L;I;-I]$, $b=[p;0;-\mathbf 1]$; by LP duality this finiteness is the finiteness of the primal minimum. The multipliers of $x\ge0$ in that dual are the slacks $c-yA_L+z$, which is why the dual of (3.3) is written with $\le c$.
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Theorem 3.1 p.8 ((3.2), (3.3), TDI, support family), §3 p.7 (the matrix A_L)

import Mathlib
import Definitions.Def_FairFlows_Covering
import Definitions.Def_BoxTDIMinMax_Separable_Setting

set_option autoImplicit false

namespace FairFlows

open Finset

variable {V A : Type}

/-- The row index set of the `(0,1)`-matrix `A_L`: the subsets `X ⊆ V` with `p(X) > −∞`
(Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, §3, p.7). The columns of
`A_L` are the edges of `L`, i.e. the subtype `↥L`; the entry at `(Z, e)` is `1` if `e` enters
`Z` and `0` otherwise. -/
abbrev LPRow (p : Finset V → WithBot ℤ) : Type := {X : Finset V // p X ≠ ⊥}

/-- The integer `p(X)` of a row `X` (finite because `p(X) > −∞`). -/
def LPRow.val' {p : Finset V → WithBot ℤ} (X : LPRow p) : ℤ :=
  (p X.1).unbotD 0

/-- `x ∈ ℝ^L` is feasible for the system `[A_L x_L ≥ p, x_L ≤ 1, x_L ≥ 0]`
(arXiv:1907.02673v5, Theorem 3.1, p.8): for every row `X`, the sum of `x` over the edges of `L`
entering `X` is at least `p(X)`, and `0 ≤ x(e) ≤ 1` for every `e ∈ L`. -/
def CoverPrimalFeasible [DecidableEq V] (D : Digraph V A) (L : Finset A)
    (p : Finset V → WithBot ℤ) (x : L → ℝ) : Prop :=
  (∀ X : LPRow p, ((X.val' : ℤ) : ℝ) ≤ ∑ e : L with D.Enters e.1 X.1, x e) ∧
  ∀ e : L, x e ≤ 1 ∧ 0 ≤ x e

/-- `x` is an optimal solution of `min{c x_L : A_L x_L ≥ p, x_L ≤ 1, x_L ≥ 0}` (for `c = 1`
this is the primal program (3.2), p.8): feasible and of least objective value among feasible
points. -/
def IsCoverPrimalOpt [DecidableEq V] (D : Digraph V A) (L : Finset A)
    (p : Finset V → WithBot ℤ) (c : L → ℝ) (x : L → ℝ) : Prop :=
  CoverPrimalFeasible D L p x ∧
  ∀ x' : L → ℝ, CoverPrimalFeasible D L p x' → ∑ e, c e * x e ≤ ∑ e, c e * x' e

/-- `(y, z) ∈ ℝ^{rows} × ℝ^L` is feasible for the dual program
`max{y p − 1 z : y A_L − z ≤ c, (y, z) ≥ 0}` (for `c = 1` this is (3.3), p.8): for every
`e ∈ L`, the sum of `y(X)` over the rows `X` entered by `e`, minus `z(e)`, is at most `c(e)`;
and `y, z ≥ 0`. -/
def CoverDualFeasible [Fintype V] [DecidableEq V] (D : Digraph V A) (L : Finset A)
    (p : Finset V → WithBot ℤ) (c : L → ℝ) (y : LPRow p → ℝ) (z : L → ℝ) : Prop :=
  (∀ e : L, (∑ X : LPRow p with D.Enters e.1 X.1, y X) - z e ≤ c e) ∧
  (∀ X, 0 ≤ y X) ∧ ∀ e, 0 ≤ z e

/-- The dual objective `y p − 1 z`. -/
def coverDualObj {L : Finset A} {p : Finset V → WithBot ℤ} [Fintype V] [DecidableEq V]
    (y : LPRow p → ℝ) (z : L → ℝ) : ℝ :=
  ∑ X, y X * ((X.val' : ℤ) : ℝ) - ∑ e, z e

/-- `(y, z)` is an optimal solution of the dual program `max{y p − 1 z : y A_L − z ≤ c,
(y, z) ≥ 0}`: feasible and of largest objective value among feasible points. -/
def IsCoverDualOpt [Fintype V] [DecidableEq V] (D : Digraph V A) (L : Finset A)
    (p : Finset V → WithBot ℤ) (c : L → ℝ) (y : LPRow p → ℝ) (z : L → ℝ) : Prop :=
  CoverDualFeasible D L p c y z ∧
  ∀ y' z', CoverDualFeasible D L p c y' z' → coverDualObj y' z' ≤ coverDualObj y z

/-- A real vector is integer-valued. -/
def IsIntegral {ι : Type} (x : ι → ℝ) : Prop :=
  ∀ i, ∃ k : ℤ, x i = (k : ℝ)

/-- The `(0,1)`-matrix `A_L` (arXiv:1907.02673v5, p.7): rows are the sets `X` with
`p(X) > −∞`, columns the edges of `L`; the entry at `(X, e)` is `1` if `e` enters `X`, else `0`. -/
def coverMatrix [DecidableEq V] (D : Digraph V A) (L : Finset A) (p : Finset V → WithBot ℤ) :
    Matrix (LPRow p) L ℚ :=
  fun X e => if D.Enters e.1 X.1 then 1 else 0

/-- The right-hand side `p` of `A_L x_L ≥ p`, as a rational vector on the rows. -/
def coverRhs (p : Finset V → WithBot ℤ) : LPRow p → ℚ :=
  fun X => ((X.val' : ℤ) : ℚ)

/-- The system `[A_L x_L ≥ p, x_L ≤ 1, x_L ≥ 0]` is totally dual integral (TDI)
(arXiv:1907.02673v5, Theorem 3.1, p.8).

**Formalization Note** This is the published `BoxTDIMinMax.Separable.IsTDI` (a rational system
`M x ≥ b` is TDI if for every integral `c` for which `max{y b : y ≥ 0, y M = c}` is finite, the
maximum has an integral optimal solution) applied to
`M = boxMat A_L = [A_L; I; −I]` and `b = boxRhs p 0 1 = [p; 0; −1]`, i.e. to the system
`A_L x ≥ p`, `x ≥ 0`, `−x ≥ −1`. By LP duality, finiteness of the dual maximum is the same as
finiteness of the primal minimum, so this is the usual notion. -/
def IsCoverTDI [Fintype V] [DecidableEq V] [DecidableEq A] (D : Digraph V A) (L : Finset A)
    (p : Finset V → WithBot ℤ) : Prop :=
  BoxTDIMinMax.Separable.IsTDI (BoxTDIMinMax.Separable.boxMat (coverMatrix D L p))
    (BoxTDIMinMax.Separable.boxRhs (coverRhs p) 0 1)

/-- The support family `{Z : y(Z) > 0}` of a dual vector `y` (arXiv:1907.02673v5, p.8). -/
def dualSupport {p : Finset V → WithBot ℤ} (y : LPRow p → ℝ) : Set (Finset V) :=
  {Z | ∃ h : p Z ≠ ⊥, 0 < y ⟨Z, h⟩}

end FairFlows


