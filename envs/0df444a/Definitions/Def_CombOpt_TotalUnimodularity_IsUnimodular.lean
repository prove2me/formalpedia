-- Prove2me | Definitions.Def_CombOpt_TotalUnimodularity_IsUnimodular
-- name    : CombOpt_TotalUnimodularity_IsUnimodular
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:19.90183+00:00
-- url     : https://prove2.me/theorems/97c70e2e-2a2d-4f15-8bdb-7f85479e1345
-- title:
--   Unimodular matrix (full row rank, every basis has determinant $\pm1$)
-- statement:
--   Let $A$ be an $m\times n$ matrix of full row rank $m$. A **basis** of $A$ is a nonsingular $m\times m$ submatrix $B$ formed by $m$ of the columns of $A$. The matrix $A$ is **unimodular** if $A$ is integral and every basis $B$ of $A$ satisfies
--   $$\det B = \pm 1.$$
--
--   Unimodularity is the condition that makes every basic solution $B^{-1}b$ of $Ax=b$ integral for integral $b$; it characterizes integrality of the polyhedra $\{x : Ax=b,\ x\ge 0\}$ (Veinott–Dantzig).
--
--   **Formalization Note** `A` has integer entries; its columns are indexed by an arbitrary finite type $\iota$ (so that $[A\ I]$, with columns `Fin n ⊕ Fin m`, is covered). Full row rank means that the real cast of $A$ has rank $m$; this is part of the predicate, since the book defines unimodularity only for matrices of full row rank. A basis is given by an injective choice $f$ of $m$ columns, in some order, with nonzero determinant; reordering the columns only changes the sign of the determinant.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.5, p. 220 (PDF p. 228)

import Mathlib

namespace CombOpt.TotalUnimodularity

/-- **Unimodular matrix (of full row rank).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.5,
p. 220 (PDF p. 228): "We call a matrix A of full row rank *unimodular* if A is integral and each
basis of A has determinant ±1." A basis of an `m × n` matrix of full row rank is a nonsingular
`m × m` submatrix formed by `m` of its columns (p. 220–221).

`IsUnimodular A` holds for an integer matrix `A` with rows `Fin m` and columns `ι` when `A` has
full row rank `m` and every square column submatrix `A.submatrix id f` (columns chosen by an
injective `f : Fin m → ι`) with nonzero determinant has determinant `1` or `-1`.

**Formalization Note.** Integrality of `A` is its type (`ℤ` entries). Full row rank is measured
over `ℝ`: the rank of the real cast of `A` is `m`. The columns of a basis are listed in the
order given by `f`; reordering them changes only the sign of the determinant, so the condition
"`± 1`" does not depend on the order. A column submatrix with nonzero integer determinant is
exactly a nonsingular one (over `ℝ`). The column index is an arbitrary finite type so that the
same notion applies to `[A I]`, whose columns are `Fin n ⊕ Fin m`. -/
def IsUnimodular {m : ℕ} {ι : Type*} [Fintype ι] (A : Matrix (Fin m) ι ℤ) : Prop :=
  (A.map (Int.cast : ℤ → ℝ)).rank = m ∧
    ∀ f : Fin m → ι, Function.Injective f → (A.submatrix id f).det ≠ 0 →
      (A.submatrix id f).det = 1 ∨ (A.submatrix id f).det = -1

end CombOpt.TotalUnimodularity


