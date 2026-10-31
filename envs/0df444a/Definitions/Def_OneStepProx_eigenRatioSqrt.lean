-- Prove2me | Definitions.Def_OneStepProx_eigenRatioSqrt
-- name    : OneStepProx_eigenRatioSqrt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:52.775995+00:00
-- url     : https://prove2.me/theorems/f5ca3479-0bcb-4342-83cc-170d30fe79ab
-- title:
--   The constant $\sqrt{\lambda_{\max}(C)/\lambda_{\min}(C)}$
-- statement:
--   For a real $d\times d$ matrix $C$, let $\lambda_{\max}(C)$ and $\lambda_{\min}(C)$ be its maximum and minimum eigenvalues. This definition is the constant
--
--   $$
--   \sqrt{\frac{\lambda_{\max}(C)}{\lambda_{\min}(C)}} .
--   $$
--
--   It is the Lipschitz constant, in the Euclidean norm, of the scaled proximal operator $\operatorname{prox}^C_h$ of a proper convex function.
--
--   **Formalization Note** The eigenvalues are the points of `spectrum ℝ C`, and $\lambda_{\max}$, $\lambda_{\min}$ are its `sSup` and `sInf`. For positive definite $C$ and $d\ge1$ the spectrum is a finite nonempty subset of $(0,\infty)$. For $d=0$ the spectrum is empty and the value is $0$; every statement using the constant is trivial there because $\mathbb R^0$ is a point.
-- source:
--   Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, proof of Theorem 2.1, p.7, "Denote by λmax(Cn) and λmin(Cn) the maximum and minimum eigenvalues of Cn"

import Mathlib

namespace OneStepProx

/-- The constant `√(λmax(C)/λmin(C))`, the square root of the ratio of the maximum and the minimum
eigenvalue of `C` (Bassett & Deride, arXiv:2004.14521v3, proof of Theorem 2.1, p.7).

**Formalization Note.** The eigenvalues of a real matrix `C` are the points of `spectrum ℝ C`, a
finite set; it is nonempty for a positive definite `C` when `d ≥ 1`, and then `sSup` and `sInf` are
its maximum and minimum, with `sInf > 0`. For `d = 0` the spectrum is empty and the value is `0`;
every statement of the mission that uses this constant is trivial in that case, since `ℝ^0` is a
single point. -/
noncomputable def eigenRatioSqrt {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt (sSup (spectrum ℝ C) / sInf (spectrum ℝ C))

end OneStepProx


