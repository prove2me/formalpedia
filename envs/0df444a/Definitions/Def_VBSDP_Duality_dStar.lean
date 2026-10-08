-- Prove2me | Definitions.Def_VBSDP_Duality_dStar
-- name    : VBSDP_Duality_dStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:28.228496+00:00
-- url     : https://prove2.me/theorems/f3a63c0e-df21-4076-9ed6-adb39a54e363
-- title:
--   Extended dual optimal value $d^*$
-- statement:
--   The **dual optimal value** is the supremum of the dual objective over all dual feasible matrices:
--
--   $$d^*=\sup\{-\operatorname{Tr}(F_0Z):Z\succeq0,\ \operatorname{Tr}(F_iZ)=c_i\ (1\le i\le m)\}.$$
--
--   The value lies in the extended real line. An empty feasible set has value $-\infty$; an unbounded-above objective has value $+\infty$.
--
--   This definition fixes the optimization model used throughout the duality mission.
--
--   **Formalization Note** Matrices have dimension $n\times n$, with coefficients $F_1,\ldots,F_m$ indexed in Lean from 0 and $F_0$ passed separately. Positive semidefiniteness and positive definiteness are matrix conditions; trace is the matrix trace.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Review 38(1) (1996), p. 64, definition of d*, PDF p. 16, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_IsDualFeasible

namespace VBSDP.Duality

noncomputable def dStar {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ) : EReal :=
  sSup ((fun Z => ((-(F₀ * Z).trace : ℝ) : EReal)) '' {Z | IsDualFeasible F c Z})

end VBSDP.Duality


