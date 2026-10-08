-- Prove2me | Definitions.Def_OTDRO_Statics_Regions
-- name    : OTDRO_Statics_Regions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:11.837261+00:00
-- url     : https://prove2.me/theorems/19917ba0-92b9-4fdf-9d13-436c1edeac46
-- title:
--   The constants K₁, K₂, δ₀, φ_min and dual regions V, W
-- statement:
--   Given lower and upper bounds $\underline L,\overline L$ on $E_{P_0}[\ell'(\beta^\top X)^2]$, this layer defines the constants $K_1,K_2$ of (28), the radius threshold $\delta_0$, and the curvature margin $\varphi_{\min}$ of §5.3. It then defines
--
--   $$\mathbb V=\{(\beta,\lambda)\in B\times\mathbb R_+:K_1\|\beta\|\le\lambda\le K_2\|\beta\|\},\qquad
--   \mathbb W=\{(\beta,\lambda)\in B\times\mathbb R_+:K_1\|\beta\|\le\lambda\le K_2R_\beta\}.$$
--
--   The layer also defines the curvature quantity $\varphi(\gamma,\beta,\lambda;x)$ of §5.3 and the section $\mathcal U(x)$: dual parameters with a scalar maximizer of positive curvature at an observation $x$ in the support of $P_0$. These regions localize dual optimizers and control the maximizer of the scalar objective.
--
--   **Formalization Note** $K_2$, $\varphi_{\min}$ and both regions depend on $\delta$; all uses assume positive $\rho_{\min}$, $\rho_{\max}$, $R_\beta$ and an appropriate small-radius condition.
-- source:
--   arXiv:1810.02403v3, (8), p. 11; (28), p. 34; §5.3, pp. 36–37

import Mathlib
import Definitions.Def_OTDRO_Statics_Assumptions
import Definitions.Def_OTDRO_StrongCvx_Regions

namespace OTDRO.Statics

open MeasureTheory

/-- The curvature quantity φ(γ,β,λ;x) of §5.3, p. 35. -/
noncomputable def phi {d : ℕ} (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ γ : ℝ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 * lam - Real.sqrt δ * OTDRO.Dual.quadInv A β x *
    deriv (deriv ℓ) (inner ℝ β x + Real.sqrt δ * γ * OTDRO.Dual.quadInv A β x)

/-- The section U(x) of the set U from §5.3, p. 35: points with a maximizer
having positive curvature, for x in the support of P₀. -/
def regionU {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d) × ℝ) :=
  {θ | x ∈ P0.support ∧ θ.1 ∈ B ∧ 0 ≤ θ.2 ∧
    ∃ γ ∈ OTDRO.Dual.maximizers ℓ A δ θ.1 θ.2 x, 0 < phi ℓ A δ γ θ.1 θ.2 x}

end OTDRO.Statics


