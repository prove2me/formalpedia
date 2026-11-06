-- Prove2me | Definitions.Def_MatrixLewis_mpow
-- name    : MatrixLewis_mpow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:24.216735+00:00
-- url     : https://prove2.me/theorems/1f58866a-cd51-45af-855d-98e6674c113b
-- title:
--   Real powers, exponential and $|Y|^q$ of a symmetric matrix
-- statement:
--   For a real symmetric matrix $A$ with spectral decomposition $A=\sum_k \lambda_k u_k u_k^\top$ and a real exponent $r$,
--   $$
--   A^r := \sum_k \lambda_k^{\,r}\, u_k u_k^\top ,
--   $$
--   defined through the continuous functional calculus. The same calculus gives the matrix exponential $e^{Y}=\sum_k e^{\lambda_k}u_ku_k^\top$ and $|Y|^q=\sum_k |\lambda_k|^q u_ku_k^\top$, where $|Y|=(Y^2)^{1/2}$.
--
--   These are the matrix functions of the paper: $S^{-1/2}$, $Z^p$, $A^{p'}$, $A^{p'-1}$, $e^{tX}$, $e^{tF/2}$ and $|G_t|^q$.
--
--   **Formalization Note** The scalar power is `Real.rpow`, so $0^r=0$ for $r>0$ (the convention of Lemma 3.13(a)); the paper takes powers only of positive semidefinite matrices, and of positive definite ones for $r\le 0$. On a non-symmetric matrix the functional calculus returns $0$, a value no statement reads.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1–3.3, pp.14–19 (S^{−1/2}, Z^p, A^{p′}); Lemmas 3.16, 3.19, 3.20, pp.25, 29, 33 (e^{tX}, |Y|^q)

import Mathlib

namespace MatrixLewis

/-- Real power `A ^ r` of a real symmetric matrix through the continuous functional calculus:
`mpow r A = cfc (fun t => t ^ r) A` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), §3.1–3.3, pp.14–19, e.g. `S^{−1/2}`, `Z^p`,
`A^{p′}`, `A^{p′−1}`).

**Formalization Note** `t ^ r` is `Real.rpow`. On a positive semidefinite `A` with spectral
decomposition `A = ∑ λₖ uₖuₖᵀ` this is `∑ λₖ^r uₖuₖᵀ`, the paper's matrix power (with
`0^r = 0` for `r > 0`, the convention of Lemma 3.13(a)); the paper only takes powers of
positive semidefinite matrices, and of positive definite ones when `r ≤ 0`. On a
non-symmetric matrix `cfc` returns `0`; no statement evaluates it there. -/
noncomputable def mpow {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ) (A : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  cfc (fun t : ℝ => t ^ r) A

/-- Matrix exponential `e^Y` of a real symmetric matrix through the continuous functional
calculus, `cfc Real.exp Y` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), §3.5–3.7, pp.25–33: `e^{tX}`, `e^{tΞ}`, `e^{tF/2}`).
For symmetric `Y` it equals the power series `∑ Yᵏ/k!`. -/
noncomputable def mexp {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  cfc Real.exp Y

/-- `|Y|^q` for a real symmetric matrix `Y`, with `|Y| = (Y²)^{1/2}` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.19,
p.29): `cfc (fun s => |s| ^ q) Y`. By the composition rule of the functional calculus this is
`((Y²)^{1/2})^q`. -/
noncomputable def mabsPow {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℝ) (Y : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  cfc (fun s : ℝ => |s| ^ q) Y

end MatrixLewis


