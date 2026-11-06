-- Prove2me | Definitions.Def_MatrixLewis_pExp
-- name    : MatrixLewis_pExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:35.696699+00:00
-- url     : https://prove2.me/theorems/10e7f874-e638-4575-9fdc-e064057b0d2d
-- title:
--   Exponents $p=q/(q-2)$ and $p'=q/2$
-- statement:
--   For the Lewis exponent $q>2$, the paper uses
--   $$
--   p:=\frac{q}{q-2},\qquad p':=\frac q2 ,
--   $$
--   so that $1/p+1/p'=1$: $p$ is the Hölder conjugate of $q/2$.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), eq. (7), p.18

import Mathlib

namespace MatrixLewis

/-- The exponent `p := q/(q − 2)` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), eq. (7), p.18), the Hölder conjugate of `q/2`. -/
noncomputable def pExp (q : ℝ) : ℝ := q / (q - 2)

/-- The exponent `p′ := q/2` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), eq. (7), p.18). -/
noncomputable def pDual (q : ℝ) : ℝ := q / 2

end MatrixLewis


