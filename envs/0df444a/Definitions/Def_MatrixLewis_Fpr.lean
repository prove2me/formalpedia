-- Prove2me | Definitions.Def_MatrixLewis_Fpr
-- name    : MatrixLewis_Fpr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:25.253856+00:00
-- url     : https://prove2.me/theorems/ce285a66-6b08-4812-951a-daddc2d355c1
-- title:
--   Primal objective $F_{\mathrm{pr}}(Z)=-\log\det H_S(Z)+\frac1p\operatorname{tr}Z^p$
-- statement:
--   For $Z\succeq0$ the **primal objective** is
--   $$
--   F_{\mathrm{pr}}(Z):=-\log\det H_S(Z)+\frac1p\operatorname{tr}Z^p ,
--   $$
--   with $F_{\mathrm{pr}}(Z):=+\infty$ when $H_S(Z)$ is singular; $F^S_{\mathrm{pr}}$ when the slack varies. So $\varphi_q(S)=-\tfrac12\inf_Z F_{\mathrm{pr}}(Z)$.
--
--   **Formalization Note** Real-valued; it is only read at $Z$ with $H_S(Z)\succ0$, where it is the paper's value.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7, p.19, eq. (10)

import Mathlib
import Definitions.Def_MatrixLewis_gram
import Definitions.Def_MatrixLewis_pExp

namespace MatrixLewis

/-- The primal objective `F_pr(Z) := −log det H_S(Z) + (1/p) tr Z^p` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Definition 3.7,
p.19, eq. (10)).

**Formalization Note** The paper sets `F_pr(Z) := +∞` when `H_S(Z)` is singular; this real
version is only read at `Z` with `H_S(Z) ≻ 0` (every statement using it assumes or proves that). -/
noncomputable def Fpr {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S Z : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -Real.log (gram A S Z).det + (1 / pExp q) * (mpow (pExp q) Z).trace

end MatrixLewis


