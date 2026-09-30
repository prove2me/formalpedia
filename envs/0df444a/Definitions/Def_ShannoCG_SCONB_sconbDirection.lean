-- Prove2me | Definitions.Def_ShannoCG_SCONB_sconbDirection
-- name    : ShannoCG_SCONB_sconbDirection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T06:52:33.072468+00:00
-- url     : https://prove2.me/theorems/058172ca-8172-4ca8-9fce-3d4be6838117
-- title:
--   Self-scaled two-update search direction $d_{k+1} = -\hat H_{k+1} g_{k+1}$
-- statement:
--   Consider a conjugate gradient cycle restarted at iteration $t$, with restart pair $(p_t, y_t)$, and a later step $k$ with step $p_k$ and gradient change $y_k$. Let $\hat H_k$ be the self-scaled restart matrix (37) built from $(p_t, y_t)$, and $\hat H_{k+1}$ its BFGS update (32) with $(p_k, y_k)$. The **self-scaled two-update search direction** at the new gradient $g_{k+1}$ is
--
--   $$d_{k+1} = -\hat H_{k+1}\, g_{k+1}.$$
--
--   This is the direction of the method (34), (38), (39) in Shanno's paper, the "far more successful" of its two double-update conjugate gradient methods; neither matrix needs to be stored, since the direction can be expanded into inner products and vectors.
--
--   **Formalization Note** Arguments are $p_t, y_t, p_k, y_k, g_{k+1}$ in this order. Equation (33) is printed with $H_{k+1}$; the context and the expansion (34) make it $\hat H_{k+1}$, which is what is used. The direction is defined as a matrix–vector product, not by the expanded formula (34).
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, pp. 249–250 (PDF pp. 6–7), §IV, eqs. (32), (33), (37)

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bfgsUpdate
import Definitions.Def_ShannoCG_SCONB_scaledRestart

open Matrix

namespace ShannoCG.SCONB

/-- The search direction of the self-scaled two-update conjugate gradient method of Shanno,
*Conjugate Gradient Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §IV,
pp. 249–250 (PDF 6–7), eqs. (37), (32), (33): at a non-restart step `k` of the restart cycle
begun at `t`, `d_{k+1} = −Ĥ_{k+1} g_{k+1}`, where `Ĥ_k` is the self-scaled restart matrix (37)
built from `(p_t, y_t)` and `Ĥ_{k+1}` is its BFGS update (32) with `(p_k, y_k)`.

**Formalization Note.** Arguments: `pt yt` = `p_t, y_t`, `pk yk` = `p_k, y_k`, `g` = `g_{k+1}`.
(33) is printed with `H_{k+1}`; the context (and the expansion (34)) make it `Ĥ_{k+1}`, which is
what is used here. The direction is defined as the matrix–vector product, not by the expanded
formula (34). -/
noncomputable def sconbDirection {n : ℕ} (pt yt pk yk g : Fin n → ℝ) : Fin n → ℝ :=
  -(bfgsUpdate (scaledRestart pt yt) pk yk *ᵥ g)

end ShannoCG.SCONB


