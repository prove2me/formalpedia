-- Prove2me | Definitions.Def_RISRO_sinTheta
-- name    : RISRO_sinTheta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:30:46.508473+00:00
-- url     : https://prove2.me/theorems/c586819d-1c21-4469-a267-b9208c6a131f
-- title:
--   Largest principal angle $\|\sin\Theta(U_1,U_2)\|$
-- statement:
--   For $U_1,U_2\in\mathbb O_{p,r}$,
--
--   $$
--   \|\sin\Theta(U_1,U_2)\|=\bigl|\sin\bigl(\cos^{-1}(\sigma_r(U_1^\top U_2))\bigr)\bigr|,
--   $$
--
--   the sine of the largest principal angle between the column spaces of $U_1$ and $U_2$.
--
--   **Formalization Note.** $\sigma_r$ is the $r$-th largest singular value, $r\ge1$.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, p.38, following display (51)

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix IRLSM.Convergence

namespace RISRO

/-- `‖sin Θ(U₁, U₂)‖ := |sin(cos⁻¹(σ_r(U₁ᵀ U₂)))|`, the sine of the largest principal angle between
the column spaces of `U₁, U₂ ∈ 𝕆_{p,r}`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, p.38 (following (51)).

Formalization Note: `σ_r` is `sv _ (r - 1)` (0-based), so `r ≥ 1` is meant; every statement using
`sinTheta` assumes `1 ≤ r`. -/
noncomputable def sinTheta {p : ℕ} (r : ℕ) (U₁ U₂ : Matrix (Fin p) (Fin r) ℝ) : ℝ :=
  |Real.sin (Real.arccos (sv (U₁ᵀ * U₂) (r - 1)))|

end RISRO


