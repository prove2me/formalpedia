-- Prove2me | Definitions.Def_VBSDP_Duality_IsDualFeasible
-- name    : VBSDP_Duality_IsDualFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:33.661991+00:00
-- url     : https://prove2.me/theorems/34301f3c-9df1-4615-8aad-29f3e064b500
-- title:
--   Dual feasibility for (27)
-- statement:
--   A symmetric matrix $Z\in\mathbb R^{n\times n}$ is **dual feasible** when
--
--   $$Z\succeq0,\qquad\operatorname{Tr}(F_iZ)=c_i\quad(1\le i\le m).$$
--
--   The positive semidefinite condition includes symmetry.
--
--   This definition fixes the optimization model used throughout the duality mission.
--
--   **Formalization Note** Matrices have dimension $n\times n$, with coefficients $F_1,\ldots,F_m$ indexed in Lean from 0 and $F_0$ passed separately. Positive semidefiniteness and positive definiteness are matrix conditions; trace is the matrix trace.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Review 38(1) (1996), p. 63, problem (27), PDF p. 15, https://doi.org/10.1137/1038003

import Mathlib

namespace VBSDP.Duality

def IsDualFeasible {m n : ℕ} (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (c : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Z.PosSemidef ∧ ∀ i, (F i * Z).trace = c i

end VBSDP.Duality


