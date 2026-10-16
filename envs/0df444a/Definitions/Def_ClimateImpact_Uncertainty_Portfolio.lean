-- Prove2me | Definitions.Def_ClimateImpact_Uncertainty_Portfolio
-- name    : ClimateImpact_Uncertainty_Portfolio
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:01.744986+00:00
-- url     : https://prove2.me/theorems/78cfd22f-9688-4277-bb31-cf26406cc0bf
-- title:
--   Proposition 5 (18)–(20), pp. 33–34 — θᵀΣ⁻¹θ, the equation for y_λ, portfolios N^{g,λ}, N^{r,λ}, global risk aversion γ*, expected returns µ
-- statement:
--   Fix a date $t$ and drop its subscript. There are $n$ assets with covariance matrix $\Sigma$. Green investors hold wealth share $\alpha\in(0,1)$ and have risk aversion $\gamma^g>0$; regular investors have risk aversion $\gamma^r>0$. Write $\theta\in\mathbb R^n$ for the green investors' vector of climate externalities $\theta_t(\psi_t)$ of the companies, and $\lambda>0$ for the intensity of the climate-information shocks: a smaller $\lambda$ means more climate uncertainty. This module defines the following objects.
--
--   1. The quadratic form $\theta^\top\Sigma^{-1}\theta$.
--   2. The predicate "$y$ solves (20)": $y>0$ and
--   $$
--   y=\exp\Big\{-\frac{\alpha\gamma^g}{\lambda}\Big(\mathbf 1^\top\theta+\frac{y}{\gamma^r}\,\theta^\top\Sigma^{-1}\theta\Big)\Big\}.
--   $$
--   3. The green investors' portfolio $N^{g,\lambda}=\alpha\big(\mathbf 1+\frac{y}{\gamma^r}\Sigma^{-1}\theta\big)$ of (19). At $y=1$ it is the portfolio $N^g$ of (11), without climate uncertainty.
--   4. The regular investors' portfolio $N^{r,\lambda}=(1-\alpha)\big(\mathbf 1-\frac{y}{\gamma^g}\Sigma^{-1}\theta\big)$ of (19).
--   5. The global risk aversion $\gamma^*$, defined by $1/\gamma^*=1/\gamma^r+1/\gamma^g$ (§2.3).
--   6. The expected-return vector $\mu=\gamma^*\Sigma\mathbf 1-\alpha y\theta$ of (18).
--
--   These objects describe the equilibrium of the market with climate uncertainty for a fixed emission schedule, in Propositions 5 and 6 and Lemma 1.
--
--   **Formalization Note** $\Sigma^{-1}$ is Mathlib's nonsingular inverse, which is $0$ for a singular matrix. Every theorem that uses these objects assumes that $\Sigma$ is positive definite. The uncertainty level is written `lam`, because `λ` is reserved in Lean.
-- source:
--   SSRN 3562534 (25 Jun 2021), Proposition 5, (18)–(20), pp. 33–34; §2.3, p. 15

import Mathlib
open Matrix

namespace ClimateImpact.Uncertainty

/-- The quadratic form `θᵀ Σ⁻¹ θ` (SSRN 3562534, (20), p. 34). `S` stands for the covariance
matrix `Σ_t`; `S⁻¹` is Mathlib's nonsingular inverse, meaningful when `S` is positive definite. -/
noncomputable def quadForm {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (θ : Fin n → ℝ) : ℝ :=
  θ ⬝ᵥ (S⁻¹ *ᵥ θ)

/-- `y` solves the one-dimensional equation (20) of Proposition 5 (p. 34) for the uncertainty
level `lam = λ` and the fixed externality vector `θ = θ_t(ψ_t)`:
`y > 0` and `y = exp{-(α γ^g / λ) (1ᵀθ + (y/γ^r) θᵀ Σ⁻¹ θ)}`. -/
def IsYLambda {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (α γr γg lam : ℝ) (θ : Fin n → ℝ)
    (y : ℝ) : Prop :=
  0 < y ∧ y = Real.exp (-(α * γg / lam) * (∑ i, θ i + y / γr * quadForm S θ))

/-- The green investors' portfolio `N^{g,λ} = α (1 + (y/γ^r) Σ⁻¹ θ)` of (19) (p. 34);
at `y = 1` it is the portfolio `N^g` of (11) without climate uncertainty. -/
noncomputable def greenPortfolio {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (α γr : ℝ)
    (θ : Fin n → ℝ) (y : ℝ) : Fin n → ℝ :=
  fun i => α * (1 + y / γr * (S⁻¹ *ᵥ θ) i)

/-- The regular investors' portfolio `N^{r,λ} = (1 - α)(1 - (y/γ^g) Σ⁻¹ θ)` of (19) (p. 34). -/
noncomputable def regularPortfolio {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (α γg : ℝ)
    (θ : Fin n → ℝ) (y : ℝ) : Fin n → ℝ :=
  fun i => (1 - α) * (1 - y / γg * (S⁻¹ *ᵥ θ) i)

/-- The global risk aversion `γ^*`, `1/γ^* = 1/γ^r + 1/γ^g` (§2.3, p. 15). -/
noncomputable def gammaStar (γr γg : ℝ) : ℝ :=
  1 / (1 / γr + 1 / γg)

/-- The expected-return vector `µ = γ^* Σ 1 - α y θ` of (18) (p. 33). -/
noncomputable def expectedReturn {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (α γr γg : ℝ)
    (θ : Fin n → ℝ) (y : ℝ) : Fin n → ℝ :=
  fun i => gammaStar γr γg * (S *ᵥ fun _ => 1) i - α * y * θ i

end ClimateImpact.Uncertainty


