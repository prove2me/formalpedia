-- Prove2me | Definitions.Def_VBSDP_Duality_IsPrimalFeasible
-- name    : VBSDP_Duality_IsPrimalFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:48.147256+00:00
-- url     : https://prove2.me/theorems/cd42550a-673a-4a53-ac9a-0c28ffc83696
-- title:
--   Primal feasibility for (1)
-- statement:
--   A vector $x\in\mathbb R^m$ is **primal feasible** when the affine matrix $F(x)$ is positive semidefinite:
--
--   $$F(x)\succeq 0.$$
--
--   This definition fixes the optimization model used throughout the duality mission.
--
--   **Formalization Note** Matrices have dimension $n\times n$, with coefficients $F_1,\ldots,F_m$ indexed in Lean from 0 and $F_0$ passed separately. Positive semidefiniteness and positive definiteness are matrix conditions; trace is the matrix trace.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Review 38(1) (1996), p. 49, problem (1), PDF p. 1, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_lmi

namespace VBSDP.Duality

def IsPrimalFeasible {m n : ℕ} (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) : Prop :=
  (lmi F₀ F x).PosSemidef

end VBSDP.Duality


