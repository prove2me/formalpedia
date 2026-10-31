-- Prove2me | Definitions.Def_ZeroOneSimplex_LPData_basicSol
-- name    : ZeroOneSimplex_LPData_basicSol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:58.922991+00:00
-- url     : https://prove2.me/theorems/db450861-0c86-47ab-b7b0-db031678ca7f
-- title:
--   Standard form, bases, basic solutions and their vertices
-- statement:
--   Adding one slack variable per inequality of $Dx\le d$ puts the LP in **standard equality form**
--   $$
--   \max\{c'^\top x' : A'x'=b',\ x'\ge 0\},\qquad A'=\begin{pmatrix}A&0\\ D&I\end{pmatrix},\ b'=\begin{pmatrix}b\\ d\end{pmatrix},\ c'=\begin{pmatrix}c\\ 0\end{pmatrix}.
--   $$
--
--   A **basis** is a set $B$ of $m+p$ columns of $A'$ that are linearly independent. Its **basic solution** $x'$ is the unique solution of $A'x'=b'$ with $x'_j=0$ for $j\notin B$; the basis is **feasible** when $x'\ge 0$. The **vertex of $P$ associated to $B$** is the original part of $x'$ (slacks removed).
--
--   **Formalization Note** Columns are indexed by `Fin n ⊕ Fin p` (originals, then slacks) and rows by `Fin m ⊕ Fin p`. The basic solution for a general right-hand side is also provided, for the lexicographic method.
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, §1.1.1, pp.6–7; §2, p.8 (vertex associated to a basis)

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData

set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

namespace LPData

variable {n m p : ℕ} (L : LPData n m p)

/-- **Standard equality form** (arXiv:2111.14050v1, §1.1.1, p.6): one slack variable per
inequality of `Dx ≤ d` gives `A' = [A 0; D I]`, with columns `Fin n ⊕ Fin p` (original
variables, then slacks) and rows `Fin m ⊕ Fin p`. The standard-form LP is
`max {c'ᵀx' : A'x' = b', x' ≥ 0}` with `c' = (c, 0)`. -/
def stdA : Matrix (Fin m ⊕ Fin p) (Fin n ⊕ Fin p) ℝ :=
  Matrix.fromBlocks L.A 0 L.D 1

/-- The right-hand side `b' = (b, d)` of the standard form (p.6). -/
def stdb : Fin m ⊕ Fin p → ℝ := Sum.elim L.b L.d

/-- **Basis** (arXiv:2111.14050v1, p.7): a set of `m + p` columns of `A'` that are linearly
independent. -/
def IsBasis (B : Finset (Fin n ⊕ Fin p)) : Prop :=
  B.card = m + p ∧ LinearIndependent ℝ (fun j : B => fun r => L.stdA r j)

open Classical in
/-- The **basic solution** of `B` for a right-hand side `r` (p.7): the unique `x'` with
`A'x' = r` and `x'_j = 0` for `j ∉ B`; it is `0` when no unique such `x'` exists (never for a
basis when `A` has full row rank). -/
noncomputable def basicSolFor (B : Finset (Fin n ⊕ Fin p)) (r : Fin m ⊕ Fin p → ℝ) :
    Fin n ⊕ Fin p → ℝ :=
  if h : ∃! x : Fin n ⊕ Fin p → ℝ, L.stdA *ᵥ x = r ∧ ∀ j, j ∉ B → x j = 0 then
    Classical.choose h.exists
  else 0

/-- The **basic solution** `x'` of the basis `B` (p.7): `x'(B) = A'_B⁻¹ b'`, `x'(N) = 0`. -/
noncomputable def basicSol (B : Finset (Fin n ⊕ Fin p)) : Fin n ⊕ Fin p → ℝ :=
  L.basicSolFor B L.stdb

/-- The **vertex of `P` associated to `B`** (arXiv:2111.14050v1, §2, p.8): the basic solution
with the slack variables removed. -/
noncomputable def vertexOf (B : Finset (Fin n ⊕ Fin p)) : Fin n → ℝ :=
  fun i => L.basicSol B (Sum.inl i)

/-- **Feasible basis** (p.7): a basis whose basic solution is nonnegative. -/
def IsFeasibleBasis (B : Finset (Fin n ⊕ Fin p)) : Prop :=
  L.IsBasis B ∧ 0 ≤ L.basicSol B

end LPData

end ZeroOneSimplex


