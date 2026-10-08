-- Prove2me | Definitions.Def_VBSDP_Duality_Zopt
-- name    : VBSDP_Duality_Zopt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:57.861254+00:00
-- url     : https://prove2.me/theorems/2b5bf49e-f7db-4029-ab0e-e6559303a3bc
-- title:
--   Dual optimal set $Z_{\mathrm{opt}}$
-- statement:
--   The **dual optimal set** contains exactly the feasible matrices attaining the dual value:
--
--   $$Z_{\mathrm{opt}}=\{Z:Z\succeq0,\ \operatorname{Tr}(F_iZ)=c_i\ (1\le i\le m),\ -\operatorname{Tr}(F_0Z)=d^*\}.$$
--
--   The set can be empty even when $d^*$ is finite.
--
--   This definition fixes the optimization model used throughout the duality mission.
--
--   **Formalization Note** Matrices have dimension $n\times n$, with coefficients $F_1,\ldots,F_m$ indexed in Lean from 0 and $F_0$ passed separately. Positive semidefiniteness and positive definiteness are matrix conditions; trace is the matrix trace.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Review 38(1) (1996), p. 64, definition of Zopt, PDF p. 16, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_dStar

namespace VBSDP.Duality

def Zopt {m n : ℕ} (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {Z | IsDualFeasible F c Z ∧ ((-(F₀ * Z).trace : ℝ) : EReal) = dStar c F₀ F}

end VBSDP.Duality


