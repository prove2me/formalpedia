-- Prove2me | Definitions.Def_NAGFlow_Implicit_ProxStep
-- name    : NAGFlow_Implicit_ProxStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:30:53.586506+00:00
-- url     : https://prove2.me/theorems/ec68aa29-c80d-44f4-b5a3-4019a9cd4977
-- title:
--   (76), p. 18 — the proximal parameter η_k and the proximal centre y_k of the implicit scheme
-- statement:
--   For real sequences $(\alpha_k),(\gamma_k)$, a constant $\mu$ and sequences $(x_k),(v_k)$ in a real Hilbert space $V$, the display after (76) on p. 18 of Luo and Chen defines
--
--   $$\eta_k=\frac{\alpha_k^2}{\gamma_k+(\mu+\gamma_k)\alpha_k},\qquad y_k=\frac{\gamma_k\alpha_kv_k+(\gamma_k+\mu\alpha_k)x_k}{\gamma_k+(\mu+\gamma_k)\alpha_k}.$$
--
--   With these, one step of the implicit scheme (72) is a proximal point step $x_{k+1}=\mathbf{prox}_{\eta_kf}(y_k)$ with proximal parameter $\eta_k$ and centre $y_k$.
--
--   **Formalization Note.** Both are plain formulas; division by the denominator is Lean's total division, and the denominator is positive whenever $\gamma_k>0$, $\mu\ge0$ and $\alpha_k>0$, which is the case in which they are used.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, (76) and the display after it, pp. 17–18

import Mathlib
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint

namespace NAGFlow.Implicit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The proximal parameter of (76), p. 18:
`η_k = α_k² / (γ_k + (μ + γ_k) α_k)`. -/
noncomputable def etaK (μ : ℝ) (α γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  α k ^ 2 / (γ k + (μ + γ k) * α k)

/-- The proximal centre of (76), p. 18:
`y_k = (γ_k α_k v_k + (γ_k + μ α_k) x_k) / (γ_k + (μ + γ_k) α_k)`. -/
noncomputable def yK (μ : ℝ) (α γ : ℕ → ℝ) (x v : ℕ → V) (k : ℕ) : V :=
  (1 / (γ k + (μ + γ k) * α k)) • ((γ k * α k) • v k + (γ k + μ * α k) • x k)

end NAGFlow.Implicit


