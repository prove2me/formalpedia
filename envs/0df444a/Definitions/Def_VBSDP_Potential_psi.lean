-- Prove2me | Definitions.Def_VBSDP_Potential_psi
-- name    : VBSDP_Potential_psi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:29.623118+00:00
-- url     : https://prove2.me/theorems/dfb799dc-dfcb-4d1c-9d47-4c4d7a5e5e7a
-- title:
--   Deviation from centrality ψ
-- statement:
--   For a strictly feasible primal-dual pair $(x,Z)$, the **deviation from centrality** is given by the explicit expression
--
--   $$\psi(x,Z)=-\log\det(F(x)Z)+n\log\operatorname{Tr}(F(x)Z)-n\log n.$$
--
--   It measures how far the pair is from a central pair with the same duality gap. Its nonnegativity is a separate milestone.
--
--   **Formalization Note** The definition uses the second equality on p. 76; the preceding expression through a central pair is not encoded. `Real.log` is total in Lean, but every theorem using $\psi$ requires strict feasibility and $n\ge1$. The indices of $F_1,\ldots,F_m$ are zero-based in Lean, with $F_0$ separate.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 76 (PDF p. 28), §4.5, ψ display, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_lmi

namespace VBSDP.Potential

/-- The explicit deviation from centrality on p. 76. -/
noncomputable def psi {m n : ℕ} (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -Real.log (VBSDP.Duality.lmi F₀ F x * Z).det +
    n * Real.log (VBSDP.Duality.lmi F₀ F x * Z).trace - n * Real.log n

end VBSDP.Potential


