-- Prove2me | Definitions.Def_ShannoCG_SCONB_bconDirection
-- name    : ShannoCG_SCONB_bconDirection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T06:56:55.669759+00:00
-- url     : https://prove2.me/theorems/406beea2-a6ca-4afd-aa6b-4eb40438ffcc
-- title:
--   Unscaled two-update search direction $d_{k+1} = -\hat H_{k+1} g_{k+1}$
-- statement:
--   Consider a conjugate gradient cycle restarted at iteration $t$, with restart pair $(p_t, y_t)$, and a later step $k$ with step $p_k$ and gradient change $y_k$. Let $\hat H_k$ be the unscaled restart matrix (31) built from $(p_t, y_t)$, and $\hat H_{k+1}$ its BFGS update (32) with $(p_k, y_k)$. The **unscaled two-update search direction** is
--
--   $$d_{k+1} = -\hat H_{k+1}\, g_{k+1}.$$
--
--   This is the direction of the method (34)–(36) in Shanno's paper, a double-update scheme first suggested by Perry.
--
--   **Formalization Note** Arguments are $p_t, y_t, p_k, y_k, g_{k+1}$ in this order. Equation (33) is printed with $H_{k+1}$ and read as $\hat H_{k+1}$. The direction is defined as a matrix–vector product, not by the expanded formulas (34)–(36).
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, pp. 249–250 (PDF pp. 6–7), §IV, eqs. (31), (32), (33)

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bfgsUpdate
import Definitions.Def_ShannoCG_SCONB_unscaledRestart

open Matrix

namespace ShannoCG.SCONB

/-- The search direction of the unscaled two-update conjugate gradient method (34)–(36) of
Shanno, *Conjugate Gradient Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §IV,
pp. 249–250 (PDF 6–7), eqs. (31), (32), (33): `d_{k+1} = −Ĥ_{k+1} g_{k+1}`, where `Ĥ_k` is the
unscaled restart matrix (31) built from `(p_t, y_t)` and `Ĥ_{k+1}` its BFGS update (32) with
`(p_k, y_k)`.

**Formalization Note.** Arguments: `pt yt` = `p_t, y_t`, `pk yk` = `p_k, y_k`, `g` = `g_{k+1}`.
(33) is printed with `H_{k+1}`, read as `Ĥ_{k+1}`. The direction is defined as the matrix–vector
product, not by the expanded formulas (34)–(36). -/
noncomputable def bconDirection {n : ℕ} (pt yt pk yk g : Fin n → ℝ) : Fin n → ℝ :=
  -(bfgsUpdate (unscaledRestart pt yt) pk yk *ᵥ g)

end ShannoCG.SCONB


