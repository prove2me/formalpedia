-- Prove2me | Definitions.Def_ZeroOneIALM_Parameters
-- name    : ZeroOneIALM_Parameters
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:29:30.94821+00:00
-- url     : https://prove2.me/theorems/ec81fa1e-b10a-49c5-bf9a-9491aaecc347
-- title:
--   The parameter choices (64), (65) and the merit value $\mathcal V_k$
-- statement:
--   Given $\mu>0$, $l_f$ and $\gamma$, put $c_1:=(\mu+l_f)/\gamma$ and $c_2:=\mu/\gamma$. The parameters are chosen as
--   $$
--   \rho>\max\Big\{\frac{16(c_1^2+c_2^2)}{\mu},\frac{6l_f}{\gamma^2}\Big\},\quad \alpha=\frac1\rho,\quad \beta:=\frac{8c_2^2}{\rho},\quad \eta>\frac{4}{\rho\gamma^2}, \tag{64}
--   $$
--   and the tolerances satisfy
--   $$
--   \frac{\epsilon_{k+1}}{\epsilon_k}\le\sqrt{\frac{\rho\gamma^2\eta-4}{\rho\gamma^2\eta+4}}. \tag{65}
--   $$
--
--   For $k\ge 1$, the **merit value** is $\mathcal V_k:=\mathcal V_{\rho,\beta}(w^k,u^k,z^k,v^{k-1})$. It uses the penalty parameter $\beta$ instead of the $\mu$ of Algorithm 1, and the Lyapunov variable $v^{k-1}$.
--
--   **Formalization Note** The value `merit … k` is used for $k\ge1$ only. The equation $\alpha=1/\rho$ is built into the IALM predicate.
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, displays (64), (65), p.21

import Mathlib
import Definitions.Def_ZeroOneIALM_Lyapunov

namespace ZeroOneIALM

variable {p n : ℕ}

/-- `c₁ := (μ + l_f)/γ`, Zhang & Xiu, arXiv:2112.00440v1, p.21. -/
noncomputable def c1 (μ lf γ : ℝ) : ℝ := (μ + lf) / γ

/-- `c₂ := μ/γ`, arXiv:2112.00440v1, p.21. -/
noncomputable def c2 (μ γ : ℝ) : ℝ := μ / γ

/-- `β := 8c₂²/ρ`, display (64), arXiv:2112.00440v1, p.21. -/
noncomputable def beta (ρ μ γ : ℝ) : ℝ := 8 * c2 μ γ ^ 2 / ρ

/-- The parameter choices (64) and (65), arXiv:2112.00440v1, p.21:
`ρ > max{16(c₁² + c₂²)/μ, 6l_f/γ²}`, `η > 4/(ργ²)` and
`ε_{k+1}/ε_k ≤ √((ργ²η - 4)/(ργ²η + 4))` for every `k`.

**Formalization Note.** `α = 1/ρ` is built into `IsIALMRun`, and `β` is `beta`, used only in
`merit`. The ratio in (65) is meaningful because `IsIALMRun` makes every `ε k` positive. -/
structure IsParameterChoice (μ lf γ ρ η : ℝ) (ε : ℕ → ℝ) : Prop where
  /-- The bound on `ρ` in (64). -/
  rho_gt : max (16 * (c1 μ lf γ ^ 2 + c2 μ γ ^ 2) / μ) (6 * lf / γ ^ 2) < ρ
  /-- The bound on `η` in (64). -/
  eta_gt : 4 / (ρ * γ ^ 2) < η
  /-- Display (65). -/
  eps_ratio : ∀ k, ε (k + 1) / ε k ≤
    Real.sqrt ((ρ * γ ^ 2 * η - 4) / (ρ * γ ^ 2 * η + 4))

/-- The merit value `V_k := V_{ρ,β}(wᵏ, uᵏ, zᵏ, vᵏ⁻¹)`, arXiv:2112.00440v1, p.21. Note the penalty
parameter `β`, not the `μ` of Algorithm 1, and the Lyapunov variable `vᵏ⁻¹`.

**Formalization Note.** The paper defines `V_k` for `k ∈ ℕ₊` only. The natural subtraction `k - 1`
is used only under `1 ≤ k`. -/
noncomputable def merit (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (lam ρ μ γ : ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin p)) (u : ℕ → EuclideanSpace ℝ (Fin n))
    (z : ℕ → EuclideanSpace ℝ (Fin n)) (v : ℕ → EuclideanSpace ℝ (Fin p)) (k : ℕ) : ℝ :=
  lyapunov f A b lam ρ (beta ρ μ γ) (w k) (u k) (z k) (v (k - 1))

end ZeroOneIALM


