-- Prove2me | Definitions.Def_PSDPolyApprox_densityMatrices
-- name    : PSDPolyApprox_densityMatrices
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:17.973149+00:00
-- url     : https://prove2.me/theorems/bfadf148-cebb-4a5e-95f9-4a363d0112ff
-- title:
--   Density matrices $\mathcal D=\{X\in S^n_+ : \operatorname{Tr}X=1\}$
-- statement:
--   The set of **density matrices** of size $n$ is
--   $$
--   \mathcal D=\{X\in S^n_+ : \operatorname{Tr}(X)=1\},
--   $$
--   where $S^n_+$ is the set of $n\times n$ real symmetric positive semidefinite matrices. Equivalently $\mathcal D=\operatorname{conv}\{xx^{\mathsf T}: x\in\mathbb R^n,\ \|x\|_2=1\}$. It is the convex body the whole paper approximates by polytopes.
--
--   **Formalization Note** A real positive semidefinite matrix in Mathlib (`Matrix.PosSemidef`) is in particular symmetric, so symmetry is not stated separately.
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §1, p.1

import Mathlib

namespace PSDPolyApprox

/-- **Density matrices** `D`.
Fawzi, *On polyhedral approximations of the positive semidefinite cone*, arXiv:1811.09649v1,
§1, p.1: "Let D be the set of positive semideﬁnite matrices of trace equal to one, also known as
the set of density of matrices: D = {X ∈ Sn+, Tr(X) = 1} … where Sn+ is the set of n × n real
symmetric positive semideﬁnite matrices."

`densityMatrices n` is the set of real `n × n` positive semidefinite matrices of trace one.

**Formalization Note.** Mathlib's `Matrix.PosSemidef` includes `IsHermitian`, which over `ℝ` is
symmetry, so no separate symmetry clause is needed. -/
def densityMatrices (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.PosSemidef ∧ X.trace = 1}

end PSDPolyApprox


