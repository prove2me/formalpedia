-- Prove2me | Definitions.Def_ShannoCG_SCONB_bealeDirection
-- name    : ShannoCG_SCONB_bealeDirection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T07:01:27.688699+00:00
-- url     : https://prove2.me/theorems/39cb601c-81ea-4ddc-8a3a-e2eda6093d42
-- title:
--   Beale's restart direction (28)
-- statement:
--   In Beale's restarted conjugate gradient method, a cycle begins at the restart iteration $t$ with direction $d_t$ and gradient change $y_t = g_{t+1} - g_t$. At a later step $k$, with previous direction $d_k$, gradient change $y_k = g_{k+1} - g_k$ and new gradient $g_{k+1}$, **Beale's direction** is
--
--   $$d_{k+1} = -g_{k+1} + \frac{y_k' g_{k+1}}{d_k' y_k}\, d_k + \frac{y_t' g_{k+1}}{d_t' y_t}\, d_t,$$
--
--   used for $k = t+1, \dots, t+n-1$. Compared with the Hestenes–Stiefel direction it carries an extra term along the restart direction $d_t$, which lets the method restart with the computed direction instead of the steepest-descent direction $-g_t$.
--
--   **Formalization Note** Arguments are $g_{k+1}, d_k, y_k, d_t, y_t$ in this order. The inner product is `⬝ᵥ`; division is total, so a vanishing denominator gives a zero coefficient.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 249 (PDF p. 6), §IV, eq. (28)

import Mathlib

open Matrix

namespace ShannoCG.SCONB

/-- Beale's restart direction, Shanno, *Conjugate Gradient Methods with Inexact Searches*,
Math. Oper. Res. 3(3) (1978), §IV, p. 249 (PDF 6), eq. (28):
`d_{k+1} = −g_{k+1} + (y_k' g_{k+1})/(d_k' y_k) · d_k + (y_t' g_{k+1})/(d_t' y_t) · d_t`,
for the non-restart steps `k = t+1, …, t+n−1` of a cycle restarted at `t`.

**Formalization Note.** Arguments: `g` = `g_{k+1}`, `dk yk` = `d_k, y_k`, `dt yt` = `d_t, y_t`.
`u'v` is `u ⬝ᵥ v`; division is total (junk value `0` when a denominator vanishes). -/
noncomputable def bealeDirection {n : ℕ} (g dk yk dt yt : Fin n → ℝ) : Fin n → ℝ :=
  -g + ((yk ⬝ᵥ g) / (dk ⬝ᵥ yk)) • dk + ((yt ⬝ᵥ g) / (dt ⬝ᵥ yt)) • dt

end ShannoCG.SCONB


