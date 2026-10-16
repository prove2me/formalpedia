-- Prove2me | Definitions.Def_ClimateImpact_Uncertainty_FixedPoint
-- name    : ClimateImpact_Uncertainty_FixedPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:44.242366+00:00
-- url     : https://prove2.me/theorems/1d7141d1-1f58-4f68-91fe-b18c3b1f34c0
-- title:
--   Proposition 7 (22), p. 37, and (23)–(24), p. 38 — schedule ψ_t(y), externality θ_t(ψ_t(y)), g*, fixed-point equation for y*_λ, condition (24)
-- statement:
--   Fix a date $t\in[0,T]$ and drop its subscript. Let $n$ companies have marginal abatement costs $c^i\ge 0$. Let the investors' externality be $\theta(x)=\kappa_0-\frac{\kappa}{2}x^2$, and let $\kappa^c$ be the curvature of the companies' externality. Let $\beta_t,\beta^c_t$ be the time factors and $\alpha$ the green investors' wealth share. This module defines the following objects.
--
--   1. The emission schedule (22) for a fixed value $y>0$ of $y_\lambda$:
--   $$
--   \psi^i_t(y)=\frac{c^i_t}{\alpha\beta_t\kappa_t\,y+\beta^c_t\kappa^c_t}.
--   $$
--   2. The externality vector $\theta_t(\psi_t(y))$, with components $\theta(\psi^i_t(y))$.
--   3. The function
--   $$
--   g^*(y)=\mathbf 1^\top\theta_t(\psi_t(y))+\frac{y}{\gamma^r}\,\theta_t(\psi_t(y))^\top\Sigma_t^{-1}\theta_t(\psi_t(y)).
--   $$
--   4. The predicate "$y$ solves the fixed-point equation (23)": $y>0$ and $y=\exp\{-\frac{\alpha\gamma^g}{\lambda}g^*(y)\}$.
--   5. Condition (24) at the date $t$:
--   $$
--   \sum_{j=1}^n(\Sigma_t^{-1})_{ij}\,y\,\theta^j_t(\psi^j_t(y))\ge-\frac{\gamma^r}{2}\qquad\text{for all } i \text{ and all } y>0.
--   $$
--   6. The externality vector $\theta_t(\psi^{*,0}_t)$ at the schedule (13) without climate uncertainty.
--
--   Equation (23) couples the companies' emission choice (22) with the green investors' internalization of climate uncertainty (20). Its solution $y^*_\lambda$ drives the equilibrium emissions.
--
--   **Formalization Note** (23) is formalized as footnote 25 derives it from (20); the printed (23) carries an extra factor $\alpha$ in the quadratic term, inconsistent with (20) and with the sign condition of (iii). The proof on p. 72 differentiates $\theta^\top\Sigma^{-1}\theta$ without the factor $2$ that the symmetry of $\Sigma^{-1}$ produces. With the corrected $g^*$, the argument of p. 72 requires the bound $-\gamma^r/2$, not the printed $-\gamma^r/\alpha$. Condition (24) is stated at the single date $t$, not for all $t\in[0,T]$, and the infimum over $y>0$ is written as a universally quantified inequality. The bound $-\gamma^r/2$ is stronger than the printed one, so the uniqueness result built on it is weaker than printed but is the one the page's argument proves.
-- source:
--   SSRN 3562534 (25 Jun 2021), Proposition 7 (22), p. 37; Proposition 8 (23)–(24), p. 38; §6.5 (48), p. 71

import Mathlib
import Definitions.Def_ClimateImpact_Interaction_TimeFactors
import Definitions.Def_ClimateImpact_Uncertainty_Portfolio
open Matrix

namespace ClimateImpact.Uncertainty

/-- The emission schedule (22) of Proposition 7 (SSRN 3562534, p. 37) at a fixed date `t`, for a
fixed value `y` of `y_λ`: `ψ^i_t(y) = c^i_t / (α β_t κ_t y + β^c_t κ^c_t)`. -/
noncomputable def schedule {n : ℕ} (ρ T t α κ κc : ℝ) (c : Fin n → ℝ) (y : ℝ) : Fin n → ℝ :=
  fun i => c i / (α * ClimateImpact.Interaction.beta ρ T t * κ * y + ClimateImpact.Interaction.betaC ρ T t * κc)

/-- The green investors' externality vector `θ_t(ψ_t(y))`, with `θ(x) = κ₀ - (κ/2) x²`
(Corollary 3, p. 20), evaluated at the schedule (22). -/
noncomputable def extAt {n : ℕ} (ρ T t α κ κc κ₀ : ℝ) (c : Fin n → ℝ) (y : ℝ) : Fin n → ℝ :=
  fun i => ClimateImpact.Interaction.quadExt κ₀ κ (schedule ρ T t α κ κc c y i)

/-- The function `g^*(y) = 1ᵀθ_t(ψ_t(y)) + (y/γ^r) θ_t(ψ_t(y))ᵀ Σ⁻¹ θ_t(ψ_t(y))` of §6.5
(p. 71), in the form obtained by plugging (22) into (20) as footnote 25 (p. 37) describes. The page
prints an extra factor `α` in the quadratic term; it is not used here. -/
noncomputable def gStar {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (γr ρ T t α κ κc κ₀ : ℝ)
    (c : Fin n → ℝ) (y : ℝ) : ℝ :=
  ∑ i, extAt ρ T t α κ κc κ₀ c y i + y / γr * quadForm S (extAt ρ T t α κ κc κ₀ c y)

/-- `y` is a positive solution of the fixed-point equation (23) (p. 38) for the uncertainty level
`lam = λ`: `y > 0` and `y = exp{-(α γ^g / λ) g^*(y)}`. -/
def IsYStar {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (γr γg lam ρ T t α κ κc κ₀ : ℝ)
    (c : Fin n → ℝ) (y : ℝ) : Prop :=
  0 < y ∧ y = Real.exp (-(α * γg / lam) * gStar S γr ρ T t α κ κc κ₀ c y)

/-- Condition (24) of Proposition 8(ii) (p. 38) at the date `t`, in the form the proof on p. 72
uses with the corrected `g^*`: for every company `i` and every `y > 0`,
`∑_j (Σ⁻¹)_{ij} y θ^j_t(ψ^j_t(y)) ≥ -γ^r/2`. -/
def Cond24 {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (γr ρ T t α κ κc κ₀ : ℝ)
    (c : Fin n → ℝ) : Prop :=
  ∀ i, ∀ y : ℝ, 0 < y → -(γr / 2) ≤ ∑ j, S⁻¹ i j * y * extAt ρ T t α κ κc κ₀ c y j

/-- The green investors' externality vector `θ_t(ψ^{*,0}_t)` at the equilibrium schedule without
climate uncertainty, `ψ^{*,0,i}_t = c^i_t (β^c_t κ^c_t + α β_t κ_t)^{-1}` of (13) (Corollary 3,
p. 20), as used in Proposition 8(iii) (p. 38). -/
noncomputable def ext0 {n : ℕ} (ρ T t α κ κc κ₀ : ℝ) (c : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ClimateImpact.Interaction.quadExt κ₀ κ (ClimateImpact.Interaction.noInteractionRate ρ T α κ κc (c i) t)

end ClimateImpact.Uncertainty


