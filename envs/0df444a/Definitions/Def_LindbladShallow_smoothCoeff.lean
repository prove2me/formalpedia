-- Prove2me | Definitions.Def_LindbladShallow_smoothCoeff
-- name    : LindbladShallow_smoothCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:10:27.751208+00:00
-- url     : https://prove2.me/theorems/8b9fe957-644a-459d-bf34-de662f8e5168
-- title:
--   The polynomials $p$, $g_N$ and the smoothed coefficients $\lambda_N$
-- statement:
--   Let $p(z)=(z^2+z^4)/2$ and $g_N(z)=\frac1N\sum_{j=0}^{N-1}z^j$. For $q\ge1$ write $p(z)^q=\sum_kc_kz^k$ (absent coefficients zero) and
--   $$\lambda_N=\frac{N}{6q}\,(c_{N-6q}-c_N),\qquad 1\le N\le 10q.$$
--
--   These are the finite-reuse combination coefficients of Lemma 4.10.
--
--   **Formalization Note** $c_{N-6q}$ is taken as $0$ when $N<6q$; polynomials have rational coefficients.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Eq. (18), p.23; Lemma 4.10, p.34

import Mathlib

open Polynomial

namespace LindbladShallow

/-- `p(z) := (z² + z⁴)/2` (arXiv:2610.05362, held version sha256 8f4637ef…, Eq. (18), p.23). -/
noncomputable def pPoly : ℚ[X] := C (1 / 2 : ℚ) * (X ^ 2 + X ^ 4)

/-- `g_N(z) := (1/N) Σ_{j=0}^{N−1} z^j` (Eq. (18), p.23). -/
noncomputable def gPoly (N : ℕ) : ℚ[X] := C (1 / (N : ℚ)) * ∑ j ∈ Finset.range N, X ^ j

/-- The coefficient `c_k` of `p(z)^q = Σ_k c_k z^k` (Lemma 4.10, p.34). -/
noncomputable def cCoef (q k : ℕ) : ℚ := (pPoly ^ q).coeff k

/-- The smoothed coefficient `λ_N := (N/(6q))(c_{N−6q} − c_N)` (Lemma 4.10, p.34), with absent
coefficients zero.

**Formalization Note** `c_{N−6q}` is written `if 6q ≤ N then c_{N−6q} else 0`, so natural-number
subtraction never truncates. -/
noncomputable def lamN (q N : ℕ) : ℚ :=
  (N : ℚ) / (6 * q) * ((if 6 * q ≤ N then cCoef q (N - 6 * q) else 0) - cCoef q N)

end LindbladShallow


