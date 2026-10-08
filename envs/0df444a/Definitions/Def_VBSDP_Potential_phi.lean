-- Prove2me | Definitions.Def_VBSDP_Potential_phi
-- name    : VBSDP_Potential_phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:20.792752+00:00
-- url     : https://prove2.me/theorems/c2e82d6d-cbd8-4da4-be54-476b84dcacbe
-- title:
--   Primal-dual potential φ in (55)
-- statement:
--   For a strictly feasible pair $(x,Z)$, a matrix size $n\ge1$, and a parameter $\nu\ge1$, the **potential** combines the logarithm of the duality gap and deviation from centrality:
--
--   $$\varphi(x,Z)=\nu\sqrt n\,\log\operatorname{Tr}(F(x)Z)+\psi(x,Z).$$
--
--   This is the quantity reduced at each step in Theorem 5.1.
--
--   **Formalization Note** The definition records the first line of (55). Theorems supply strict feasibility and $\nu\ge1$; the total real logarithm has no intended meaning outside that domain. $n$ is the matrix size, and Lean indexes $F_1,\ldots,F_m$ from zero with $F_0$ separate.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 76 (PDF p. 28), (55), https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Potential_psi

namespace VBSDP.Potential

/-- The potential in the first line of (55). -/
noncomputable def phi {m n : ℕ} (ν : ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ν * Real.sqrt n * Real.log (VBSDP.Duality.lmi F₀ F x * Z).trace + psi F₀ F x Z

end VBSDP.Potential


