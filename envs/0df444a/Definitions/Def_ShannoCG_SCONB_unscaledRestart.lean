-- Prove2me | Definitions.Def_ShannoCG_SCONB_unscaledRestart
-- name    : ShannoCG_SCONB_unscaledRestart
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T06:49:55.469984+00:00
-- url     : https://prove2.me/theorems/c8b12b42-2b43-4ac8-b28d-c7215786f49c
-- title:
--   Unscaled restart matrix $\hat H_k$ of (31)
-- statement:
--   Let $p_t, y_t \in \mathbb R^n$ be the restart step and gradient change of a conjugate gradient cycle restarted at iteration $t$. The **unscaled restart matrix** is the BFGS update of the identity with $(p_t, y_t)$:
--
--   $$\hat H_k = I - \frac{p_t y_t' + y_t p_t'}{p_t' y_t} + \left(1 + \frac{y_t' y_t}{p_t' y_t}\right)\frac{p_t p_t'}{p_t' y_t}.$$
--
--   It is the first of the two updates in Shanno's unscaled double-update conjugate gradient method (34)–(36), a two-vector analogue of the memoryless BFGS direction.
--
--   **Formalization Note** Defined literally as printed in (31). $uv'$ is `vecMulVec u v`, $u'v$ is `u ⬝ᵥ v`, $I$ is `1`. Division is total; theorems using this matrix assume $p_t'y_t \ne 0$ or $p_t'y_t > 0$.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 249 (PDF p. 6), §IV, eq. (31)

import Mathlib

open Matrix

namespace ShannoCG.SCONB

/-- The unscaled restart matrix of Shanno, *Conjugate Gradient Methods with Inexact Searches*,
Math. Oper. Res. 3(3) (1978), §IV, p. 249 (PDF 6), eq. (31) — the BFGS update (16) of the
identity with the restart pair `(p_t, y_t)`:
`Ĥ_k = I − (p_t y_t' + y_t p_t') / (p_t' y_t) + (1 + y_t' y_t / p_t' y_t) · p_t p_t' / (p_t' y_t)`.

**Formalization Note.** Written literally as printed in (31). `uv'` is `vecMulVec u v`, `u'v` is
`u ⬝ᵥ v`, `I` is `1`. Division is total; theorems using this matrix assume `p_t ⬝ᵥ y_t ≠ 0`
(or `> 0`). -/
noncomputable def unscaledRestart {n : ℕ} (p y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 : Matrix (Fin n) (Fin n) ℝ)
    - (1 / (p ⬝ᵥ y)) • (vecMulVec p y + vecMulVec y p)
    + ((1 + (y ⬝ᵥ y) / (p ⬝ᵥ y)) * (1 / (p ⬝ᵥ y))) • vecMulVec p p

end ShannoCG.SCONB


