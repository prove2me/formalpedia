-- Prove2me | Definitions.Def_VBSDP_Duality_Xopt
-- name    : VBSDP_Duality_Xopt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:59.273899+00:00
-- url     : https://prove2.me/theorems/09066f7d-839f-4c14-8c97-b5b3e7573822
-- title:
--   Primal optimal set $X_{\mathrm{opt}}$
-- statement:
--   The **primal optimal set** contains exactly the feasible vectors attaining the primal value:
--
--   $$X_{\mathrm{opt}}=\{x:F(x)\succeq0,\ c^Tx=p^*\}.$$
--
--   The set can be empty even when $p^*$ is finite.
--
--   This definition fixes the optimization model used throughout the duality mission.
--
--   **Formalization Note** Matrices have dimension $n\times n$, with coefficients $F_1,\ldots,F_m$ indexed in Lean from 0 and $F_0$ passed separately. Positive semidefiniteness and positive definiteness are matrix conditions; trace is the matrix trace.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Review 38(1) (1996), p. 64, definition of Xopt, PDF p. 16, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_pStar

namespace VBSDP.Duality

def Xopt {m n : ℕ} (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) : Set (Fin m → ℝ) :=
  {x | IsPrimalFeasible F₀ F x ∧ ((c ⬝ᵥ x : ℝ) : EReal) = pStar c F₀ F}

end VBSDP.Duality


