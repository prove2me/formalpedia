-- Prove2me | Definitions.Def_MarkovSA_T4
-- name    : MarkovSA_T4
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:21.593503+00:00
-- url     : https://prove2.me/theorems/d6532639-d7bd-4626-9858-7fc9e3d4bd1f
-- title:
--   $T_4=\frac{L\alpha_k^2}{2\theta}\|F(x_k,Y_k)-x_k+w_k\|_s^2$
-- statement:
--   The discretization term of (17):
--
--   $$
--   T_4=\frac{L\alpha_k^2}{2\theta}\,\|F(x_k,Y_k)-x_k+w_k\|_s^2.
--   $$
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Eq. (17), p.25

import Mathlib

namespace MarkovSA

/-- `T₄ = (L α_k²/(2θ)) ‖F(x_k, Y_k) − x_k + w_k‖_s²`, the discretization term of Eq. (17) (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.25). -/
noncomputable def T4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] {Ω : Type*} (s : E → ℝ) (L θ : ℝ)
    (F : E → 𝒴 → E) (α : ℕ → ℝ) (x : ℕ → Ω → E) (Y : ℕ → Ω → 𝒴) (w : ℕ → Ω → E)
    (k : ℕ) (ω : Ω) : ℝ :=
  L * α k ^ 2 / (2 * θ) * s (F (x k ω) (Y k ω) - x k ω + w k ω) ^ 2

end MarkovSA


