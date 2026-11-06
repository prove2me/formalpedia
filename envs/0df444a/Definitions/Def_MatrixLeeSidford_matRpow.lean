-- Prove2me | Definitions.Def_MatrixLeeSidford_matRpow
-- name    : MatrixLeeSidford_matRpow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:16.171943+00:00
-- url     : https://prove2.me/theorems/e5400f44-34e7-4532-8324-85c071bd545c
-- title:
--   Real power $D^r$ of a symmetric matrix
-- statement:
--   For a real symmetric matrix $D=U\operatorname{diag}(\lambda_i)U^\top$ and $r\in\mathbb R$, the **real power** is
--   $$
--   D^r=U\operatorname{diag}(\lambda_i^r)U^\top .
--   $$
--   For $D\succ0$ this is defined for every real $r$; in particular $D^{-1/2}$ is the inverse of the positive square root. For $D\succeq0$ and $r>0$ it is the usual power, e.g. the positive semidefinite square root $D^{1/2}$ and $W^{s/(s-1)}$.
--
--   **Formalization Note** Implemented by Mathlib's continuous functional calculus for Hermitian matrices applied to $x\mapsto x^r$; it is only used on positive (semi)definite arguments.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Section 3.3, p.31

import Mathlib

open Matrix

namespace MatrixLeeSidford

/-- Real powers of a symmetric matrix through its spectral decomposition: for
`D = U diag(λᵢ) Uᵀ`, `D^r := U diag(λᵢ^r) Uᵀ` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Section 3.3, p.31: "positive definite
matrices have well-defined real powers, logarithms, and positive square roots").

**Formalization Note** Implemented with Mathlib's continuous functional calculus `cfc` for
Hermitian matrices, applied to `x ↦ x ^ r` (`Real.rpow`). On a positive definite matrix this is
the paper's `D^r` for every real `r` (so `S^{-1/2}` is `matRpow (-1/2) S`); on a positive
semidefinite matrix it is the paper's power for `r > 0` (so `G^{1/2}`, `W^{s/(s−1)}` are
`matRpow (1/2) G`, `matRpow (s/(s−1)) W`). On a non-symmetric matrix `cfc` returns `0`; every use
in this mission is on a positive (semi)definite matrix. -/
noncomputable def matRpow {k : ℕ} (r : ℝ) (D : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  cfc (fun x : ℝ => x ^ r) D

end MatrixLeeSidford


