-- Prove2me | Definitions.Def_OTDRO_StrongCvx_Regions
-- name    : OTDRO_StrongCvx_Regions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:30.044547+00:00
-- url     : https://prove2.me/theorems/2dd0965e-9805-4330-8b6e-9e8403cf17ec
-- title:
--   Constants K₁, K₂, δ₀, φmin and regions V and W
-- statement:
--   Let $\underline L,\overline L$ bound the expectation of $\ell'(\beta^{\mathsf T}X)^2$ on $B$, and let $R_\beta=\sup_{\beta\in B}\|\beta\|$. The paper's explicit constants are
--
--   $$K_1=\tfrac12\sqrt{\underline L/\rho_{\max}},\quad K_2=\tfrac12\sqrt\delta M R_\beta/\rho_{\min}+\sqrt{\overline L/\rho_{\min}},\quad \delta_0=\frac{\rho_{\min}^2\underline L}{R_\beta^2M^2\rho_{\max}}.$$
--
--   The region containing the dual optimizers is $\mathbb V=\{(\beta,\lambda):\beta\in B,\lambda\ge0,K_1\|\beta\|\le\lambda\le K_2\|\beta\|\}$. The wider region $\mathbb W$ replaces the last upper bound by $K_2R_\beta$. The margin $\varphi_{\min}=\sqrt{\underline L}/\sqrt{\rho_{\max}}-\sqrt\delta R_\beta M/\rho_{\min}$ is used on $\mathbb W$.
--
--   These quantities locate the region and radius in Theorems 3–4.
--
--   **Formalization Note** The real supremum defining $R_\beta$ is used with nonempty compact $B$; the reciprocal formulas are used where their denominators are positive.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, (8), p. 11; (28), p. 34; §5.3, p. 36

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_Assumptions

namespace OTDRO.StrongCvx

/-- K₁ = 1/2 √(L̲/ρmax), display (28), p. 34. -/
noncomputable def K1 (Llow ρmax : ℝ) : ℝ :=
  (1 / 2) * Real.sqrt (Llow / ρmax)

/-- K₂ = 1/2 √δ M R_β / ρmin + √(L̄/ρmin), display (28), p. 34. -/
noncomputable def K2 (δ M R ρmin Lbar : ℝ) : ℝ :=
  (1 / 2) * Real.sqrt δ * M * R / ρmin + Real.sqrt (Lbar / ρmin)

/-- δ₀ = ρmin² L̲ / (R_β² M² ρmax), p. 36. -/
noncomputable def delta0 (ρmin ρmax Llow R M : ℝ) : ℝ :=
  ρmin ^ 2 * Llow / (R ^ 2 * M ^ 2 * ρmax)

/-- φmin = √L̲ / √ρmax − √δ R_β M / ρmin, p. 36. -/
noncomputable def phiMin (δ Llow ρmax R M ρmin : ℝ) : ℝ :=
  Real.sqrt Llow / Real.sqrt ρmax - Real.sqrt δ * R * M / ρmin

/-- The region V of (8), pp. 11 and 36, with K₁ and K₂ fixed by (28). -/
def regionV {d : ℕ} (B : Set (EuclideanSpace ℝ (Fin d)))
    (δ M R ρmin ρmax Llow Lbar : ℝ) :
    Set (EuclideanSpace ℝ (Fin d) × ℝ) :=
  {θ | θ.1 ∈ B ∧ 0 ≤ θ.2 ∧
    K1 Llow ρmax * ‖θ.1‖ ≤ θ.2 ∧
    θ.2 ≤ K2 δ M R ρmin Lbar * ‖θ.1‖}

/-- The wider region W of p. 36. -/
def regionW {d : ℕ} (B : Set (EuclideanSpace ℝ (Fin d)))
    (δ M R ρmin ρmax Llow Lbar : ℝ) :
    Set (EuclideanSpace ℝ (Fin d) × ℝ) :=
  {θ | θ.1 ∈ B ∧ 0 ≤ θ.2 ∧
    K1 Llow ρmax * ‖θ.1‖ ≤ θ.2 ∧
    θ.2 ≤ K2 δ M R ρmin Lbar * R}

end OTDRO.StrongCvx


