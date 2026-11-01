-- Prove2me | Definitions.Def_ALAVI_lam
-- name    : ALAVI_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:38.235798+00:00
-- url     : https://prove2.me/theorems/f760cd8a-73c3-40ef-9293-857076c7e087
-- title:
--   The Lyapunov function $\Lambda^k(u,p)$ (31)
-- statement:
--   For a run of ALAVI and $k\ge1$, the **Lyapunov function** is
--
--   $$
--   \Lambda^k(u,p)=\beta_1\|v^k-u\|^2+\beta_2\|u^{k-1}-u^k\|^2+\beta_3\|p^{k-1}-p\|^2,\qquad
--   \beta_1=\frac1{2\alpha(1-\eta)},\ \beta_2=\frac{\gamma\tau^2+L+\tau}2,\ \beta_3=\frac1{2\gamma}.
--   $$
--
--   **Formalization Note.** Used only at $k\ge1$ (indices are natural numbers).
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, display (31), p.13

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj

namespace ALAVI

/-- **The Lyapunov function (31)**,
`Λᵏ(w, b) = β₁‖vᵏ - w‖² + β₂‖uᵏ⁻¹ - uᵏ‖² + β₃‖pᵏ⁻¹ - b‖²` with `β₁ = 1/(2α(1 - η))`,
`β₂ = (γτ² + L + τ)/2` and `β₃ = 1/(2γ)`.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, (31), p.13.

Formalization Note: used only at `k ≥ 1` (at `k = 0`, `k - 1` is `0` in `ℕ`). -/
noncomputable def lam {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (η α γ L τ : ℝ) (v u : ℕ → E) (p : ℕ → F) (k : ℕ) (w : E) (b : F) : ℝ :=
  1 / (2 * α * (1 - η)) * ‖v k - w‖ ^ 2 + (γ * τ ^ 2 + L + τ) / 2 * ‖u (k - 1) - u k‖ ^ 2 +
    1 / (2 * γ) * ‖p (k - 1) - b‖ ^ 2

end ALAVI


