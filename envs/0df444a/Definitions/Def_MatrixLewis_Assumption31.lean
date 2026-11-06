-- Prove2me | Definitions.Def_MatrixLewis_Assumption31
-- name    : MatrixLewis_Assumption31
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:29.274463+00:00
-- url     : https://prove2.me/theorems/c4681513-8d3a-4f05-a946-6ea0817b5d6f
-- title:
--   Assumption 3.1 — standing nondegeneracy and support reduction
-- statement:
--   Data $A_1,\dots,A_m\in\mathbb R^{n\times n}$ satisfy **Assumption 3.1** if
--
--   1. $A_1,\dots,A_m$ are linearly independent, and
--   2. $\bigcap_{i=1}^m \ker A_i=\{0\}$: the only $v\in\mathbb R^n$ with $A_iv=0$ for every $i$ is $v=0$.
--
--   The paper assumes it throughout Section 3; a standard reduction enforces both conditions.
--
--   **Formalization Note** Symmetry of the $A_i$ (the paper's $A_i\in\mathbb S^n$) is not part of this predicate; every statement of the mission assumes it separately.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Assumption 3.1, p.15

import Mathlib

namespace MatrixLewis

/-- **Assumption 3.1** (Standing nondegeneracy and support reduction; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), p.15):
the matrices `A₁, …, A_m` are linearly independent, and `⋂ᵢ ker Aᵢ = {0}`.

**Formalization Note** The data `A : Fin m → Matrix (Fin n) (Fin n) ℝ`; the paper's
`A₁, …, A_m ∈ Sⁿ` (symmetry) is a separate hypothesis `∀ i, (A i).IsHermitian` of every
statement. The trivial common kernel is: every `v ∈ ℝⁿ` with `Aᵢ v = 0` for all `i` is `0`. -/
def Assumption31 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  LinearIndependent ℝ A ∧ ∀ v : Fin n → ℝ, (∀ i, (A i).mulVec v = 0) → v = 0

end MatrixLewis


