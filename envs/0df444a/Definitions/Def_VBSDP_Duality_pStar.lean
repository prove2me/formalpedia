-- Prove2me | Definitions.Def_VBSDP_Duality_pStar
-- name    : VBSDP_Duality_pStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:00.578021+00:00
-- url     : https://prove2.me/theorems/78584491-5091-49f3-93f7-e8f4fc205671
-- title:
--   Extended primal optimal value $p^*$
-- statement:
--   The **primal optimal value** is the infimum of the linear objective over all primal feasible vectors:
--
--   $$p^*=\inf\{c^Tx:F(x)\succeq0\}.$$
--
--   The value lies in the extended real line. An empty feasible set has value $+\infty$; an unbounded-below objective has value $-\infty$.
--
--   This definition fixes the optimization model used throughout the duality mission.
--
--   **Formalization Note** Matrices have dimension $n\times n$, with coefficients $F_1,\ldots,F_m$ indexed in Lean from 0 and $F_0$ passed separately. Positive semidefiniteness and positive definiteness are matrix conditions; trace is the matrix trace.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Review 38(1) (1996), p. 64, definition of p*, PDF p. 16, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_IsPrimalFeasible

namespace VBSDP.Duality

noncomputable def pStar {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ) : EReal :=
  sInf ((fun x => ((c ⬝ᵥ x : ℝ) : EReal)) '' {x | IsPrimalFeasible F₀ F x})

end VBSDP.Duality


