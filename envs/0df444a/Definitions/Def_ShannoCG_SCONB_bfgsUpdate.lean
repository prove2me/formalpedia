-- Prove2me | Definitions.Def_ShannoCG_SCONB_bfgsUpdate
-- name    : ShannoCG_SCONB_bfgsUpdate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T06:41:52.428394+00:00
-- url     : https://prove2.me/theorems/f715438d-dc3e-4f20-ae43-43b355aafd6d
-- title:
--   BFGS inverse-Hessian update, additive form (16)/(32)
-- statement:
--   Let $H$ be a real $n\times n$ matrix and $p, y \in \mathbb R^n$. The **BFGS update** of $H$ with the pair $(p, y)$ is the matrix
--
--   $$H^{+} = H - \frac{p\,y'H + H y\,p'}{p'y} + \left(1 + \frac{y'Hy}{p'y}\right)\frac{p\,p'}{p'y},$$
--
--   where $u'v$ is the inner product and $uv'$ the outer product. In a quasi-Newton or conjugate gradient iteration $p = p_k = x_{k+1} - x_k$ is the step and $y = y_k = g_{k+1} - g_k$ the change of gradient; the update makes $H^+ y = p$ hold whenever $p'y \ne 0$.
--
--   This is the form in which Shanno writes the Broyden–Fletcher–Goldfarb–Shanno inverse update (16) and its use in the double-update conjugate gradient methods (32).
--
--   **Formalization Note** Vectors are `Fin n → ℝ`; $uv'$ is `vecMulVec u v`, $Hy$ is `H *ᵥ y` and $y'H$ is `y ᵥ* H`. No symmetry of $H$ is assumed: the two middle terms are written exactly as printed. Division is total, so when $p'y = 0$ the matrix is a junk value; theorems about the update assume $p'y \neq 0$ or $p'y > 0$ where it matters.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 246 (PDF p. 3), §II, eq. (16); p. 250 (PDF p. 7), §IV, eq. (32)

import Mathlib

open Matrix

namespace ShannoCG.SCONB

/-- The BFGS inverse-Hessian update in the additive form of Shanno, *Conjugate Gradient Methods
with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §II, p. 246 (PDF 3), eq. (16), and §IV,
p. 250 (PDF 7), eq. (32):
`Ĥ_{k+1} = Ĥ_k − (p_k y_k' Ĥ_k + Ĥ_k y_k p_k') / (p_k' y_k)
  + (1 + y_k' Ĥ_k y_k / p_k' y_k) · p_k p_k' / (p_k' y_k)`.

**Formalization Note.** Vectors are `Fin n → ℝ`; the inner product `u'v` is `u ⬝ᵥ v`, the outer
product `uv'` is `vecMulVec u v`, `Ĥ y` is `H *ᵥ y` and `y'Ĥ` is `y ᵥ* H`. No symmetry of `H` is
assumed: the two middle terms are written exactly as in (32). Division is Lean's total division, so
the value when `p ⬝ᵥ y = 0` is a junk value; every theorem using the update assumes a nonzero (in
fact positive) curvature `p ⬝ᵥ y` where it matters. -/
noncomputable def bfgsUpdate {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (p y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  H - (1 / (p ⬝ᵥ y)) • (vecMulVec p (y ᵥ* H) + vecMulVec (H *ᵥ y) p)
    + ((1 + (y ⬝ᵥ (H *ᵥ y)) / (p ⬝ᵥ y)) * (1 / (p ⬝ᵥ y))) • vecMulVec p p

end ShannoCG.SCONB


