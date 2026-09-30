-- Prove2me | Definitions.Def_ShannoCG_SCONB_gammaScale
-- name    : ShannoCG_SCONB_gammaScale
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T06:39:02.791464+00:00
-- url     : https://prove2.me/theorems/948fb154-9f13-4050-bbaf-fc492cfbd123
-- title:
--   Oren–Spedicato scale factor $\gamma_t = p_t'y_t / y_t'y_t$
-- statement:
--   For vectors $p, y \in \mathbb R^n$ the **scale factor** is
--
--   $$\gamma = \frac{p'y}{y'y},$$
--
--   where $u'v$ denotes the Euclidean inner product. In Shanno's self-scaled conjugate gradient method it is evaluated at the restart pair, $\gamma_t = p_t'y_t / y_t'y_t$, where $p_t = x_{t+1} - x_t$ is the restart step and $y_t = g_{t+1} - g_t$ the corresponding change of gradient.
--
--   The factor rescales the identity matrix before the first quasi-Newton update of a restart cycle; on a quadratic with exact searches it becomes the length factor by which the method's search direction differs from Beale's.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ` and the inner product is `⬝ᵥ`. Lean's division is total, so the value is $0$ when $y = 0$; every theorem that uses $\gamma$ assumes $p'y \neq 0$ or $p'y > 0$, which forces $y \neq 0$.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 250 (PDF p. 7), §IV, the line after eq. (37); cf. §III, eq. (23)

import Mathlib

open Matrix

namespace ShannoCG.SCONB

/-- The Oren–Spedicato scale factor `γ_t = p_t' y_t / y_t' y_t` of Shanno, *Conjugate Gradient
Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §III, (23), and §IV, p. 250
(PDF 7), the line after eq. (37).

**Formalization Note.** Vectors are `Fin n → ℝ` and `u'v` is `u ⬝ᵥ v`. Lean's division is total:
`gammaScale p y = 0` when `y = 0`. -/
noncomputable def gammaScale {n : ℕ} (p y : Fin n → ℝ) : ℝ :=
  (p ⬝ᵥ y) / (y ⬝ᵥ y)

end ShannoCG.SCONB


