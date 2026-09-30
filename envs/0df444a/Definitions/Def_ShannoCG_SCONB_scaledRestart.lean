-- Prove2me | Definitions.Def_ShannoCG_SCONB_scaledRestart
-- name    : ShannoCG_SCONB_scaledRestart
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T06:47:07.535854+00:00
-- url     : https://prove2.me/theorems/109cfaa1-907a-4c16-ab36-d777d9c3c637
-- title:
--   Self-scaled restart matrix $\hat H_k$ of (37)
-- statement:
--   Let $p_t, y_t \in \mathbb R^n$ be the restart step and gradient change of a conjugate gradient cycle restarted at iteration $t$, and $\gamma_t = p_t'y_t / y_t'y_t$. The **self-scaled restart matrix** is
--
--   $$\hat H_k = \gamma_t\left(I - \frac{p_t y_t' + y_t p_t'}{p_t' y_t} + \frac{y_t' y_t}{p_t' y_t}\,\frac{p_t p_t'}{p_t' y_t}\right) + \frac{p_t p_t'}{p_t' y_t}.$$
--
--   It depends only on the restart pair $(p_t, y_t)$, so it is the same matrix for every step $k$ of the restart cycle (the subscript $k$ is the paper's). It is the BFGS update of $\gamma_t I$ with $(p_t, y_t)$, and it is the first of the two updates that define Shanno's self-scaled conjugate gradient direction.
--
--   **Formalization Note** Defined literally as printed in (37), not as a BFGS update of $\gamma_t I$. $uv'$ is `vecMulVec u v`, $u'v$ is `u ⬝ᵥ v`, $I$ is `1`. Division is total; theorems using this matrix assume $p_t'y_t \ne 0$ or $p_t'y_t > 0$.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 250 (PDF p. 7), §IV, eq. (37)

import Mathlib
import Definitions.Def_ShannoCG_SCONB_gammaScale

open Matrix

namespace ShannoCG.SCONB

/-- The self-scaled restart matrix of Shanno, *Conjugate Gradient Methods with Inexact Searches*,
Math. Oper. Res. 3(3) (1978), §IV, p. 250 (PDF 7), eq. (37):
`Ĥ_k = γ_t (I − (p_t y_t' + y_t p_t') / (p_t' y_t) + (y_t' y_t / p_t' y_t) · p_t p_t' / (p_t' y_t))
  + p_t p_t' / (p_t' y_t)`, with `γ_t = p_t' y_t / y_t' y_t`.
It depends only on the restart pair `(p_t, y_t)`.

**Formalization Note.** Written literally as printed in (37) (not as a BFGS update of `γ_t I`,
to which it is equal when `p_t' y_t ≠ 0`). `uv'` is `vecMulVec u v`, `u'v` is `u ⬝ᵥ v`, `I` is
`1`. Division is total; theorems using this matrix assume `p_t ⬝ᵥ y_t ≠ 0` (or `> 0`). -/
noncomputable def scaledRestart {n : ℕ} (p y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  gammaScale p y • ((1 : Matrix (Fin n) (Fin n) ℝ)
      - (1 / (p ⬝ᵥ y)) • (vecMulVec p y + vecMulVec y p)
      + ((y ⬝ᵥ y) / (p ⬝ᵥ y) * (1 / (p ⬝ᵥ y))) • vecMulVec p p)
    + (1 / (p ⬝ᵥ y)) • vecMulVec p p

end ShannoCG.SCONB


