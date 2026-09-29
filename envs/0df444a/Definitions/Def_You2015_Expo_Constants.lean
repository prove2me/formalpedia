-- Prove2me | Definitions.Def_You2015_Expo_Constants
-- name    : You2015_Expo_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:09:26.978983+00:00
-- url     : https://prove2.me/theorems/d483c28b-fc3c-4f4b-ad69-56aa34d840b6
-- title:
--   The constants θ, λ of Theorem 4.2, H₁ (corrected) and H₂ of (4.5), and the left-hand side of the rate equation (4.4)
-- statement:
--   Let $K_1,K_2,K_3,\lambda_1,\lambda_2,c_2>0$ and $\tau>0$ be the constants of Assumptions 2.1, 2.2, 3.1, 4.1 and of the observation interval. This file defines
--   $$\theta=\frac{K_3^2}{\lambda_1},\qquad\lambda=\lambda_2-\theta\tau\big[2\tau(K_1^2+2K_3^2)+K_2^2\big]\tag{3.14, 3.16}$$
--   and the two constants of (4.5),
--   $$H_1=\theta\tau\big(2\tau(K_1^2+2K_3^2)+K_2^2\big)+\frac{24\,\theta\tau^4K_3^4}{1-6\tau^2K_3^2},\qquad H_2=\frac{12\theta\tau^2K_3^2(\tau K_1^2+K_2^2)}{1-6\tau^2K_3^2},$$
--   together with the function
--   $$\gamma\longmapsto2\tau\gamma e^{2\tau\gamma}(H_1+\tau H_2)+\gamma c_2,$$
--   the left-hand side of equation (4.4), whose unique positive root $\gamma$ with right-hand side $\lambda$ is the exponential rate of Theorem 4.2.
--
--   **Correction of (4.5).** The page prints the second term of $H_1$ as $\frac{24\tau^3K_3^4}{1-6\tau^2K_3^2}$. The proof of Theorem 4.2 obtains $H_1$ by substituting (3.21) into (4.9): the term $4\tau K_3^2\,\mathbb E|x(v)-x(\delta_v)|^2$ inside $\theta\tau\int[\cdots]dv$ contributes $\theta\tau\cdot4\tau K_3^2\cdot\frac{6\tau^2K_3^2}{1-6\tau^2K_3^2}=\frac{24\theta\tau^4K_3^4}{1-6\tau^2K_3^2}$. The same computation reproduces the printed $H_2$ exactly, which confirms that the printed $H_1$ lost the factor $\theta\tau$. The definition here uses the corrected value.
--
--   **Formalization Note** Under (3.5), $\tau\le1/(4K_3)$ gives $6\tau^2K_3^2\le3/8<1$, so the divisions are by a positive number wherever the constants are used. $\lambda_1,\lambda_2$ are written `lam₁`, `lam₂`, and $\lambda$ is `lam`.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, p. 911, Eqs. (3.14), (3.16); pp. 917–918, Theorem 4.2 (θ, λ, Eqs. (4.4)–(4.5); H₁ corrected, see the statement)

import Mathlib

open scoped NNReal

namespace You2015.Expo

/-- `θ = K₃²/λ₁` ((3.16) and Theorem 4.2). -/
noncomputable def theta (K₃ lam₁ : ℝ) : ℝ := K₃ ^ 2 / lam₁

/-- `λ = λ(θ, τ) = λ₂ − θτ[2τ(K₁² + 2K₃²) + K₂²]` ((3.14) and Theorem 4.2), with `θ = K₃²/λ₁`. -/
noncomputable def lam (K₁ K₂ K₃ lam₁ lam₂ : ℝ) (τ : ℝ≥0) : ℝ :=
  lam₂ - theta K₃ lam₁ * τ * (2 * τ * (K₁ ^ 2 + 2 * K₃ ^ 2) + K₂ ^ 2)

/-- The constant `H₁` of (4.5), **as the proof of Theorem 4.2 uses it**:
`H₁ = θτ(2τ(K₁² + 2K₃²) + K₂²) + 24θτ⁴K₃⁴/(1 − 6τ²K₃²)`. The page prints `24τ³K₃⁴` for the
last numerator; (4.9) combined with (3.21) gives `θτ · 4τK₃² · 6τ²K₃² = 24θτ⁴K₃⁴`. -/
noncomputable def H1 (K₁ K₂ K₃ lam₁ : ℝ) (τ : ℝ≥0) : ℝ :=
  theta K₃ lam₁ * τ * (2 * τ * (K₁ ^ 2 + 2 * K₃ ^ 2) + K₂ ^ 2)
    + 24 * theta K₃ lam₁ * (τ : ℝ) ^ 4 * K₃ ^ 4 / (1 - 6 * (τ : ℝ) ^ 2 * K₃ ^ 2)

/-- The constant `H₂ = 12θτ²K₃²(τK₁² + K₂²)/(1 − 6τ²K₃²)` of (4.5). -/
noncomputable def H2 (K₁ K₂ K₃ lam₁ : ℝ) (τ : ℝ≥0) : ℝ :=
  12 * theta K₃ lam₁ * (τ : ℝ) ^ 2 * K₃ ^ 2 * (τ * K₁ ^ 2 + K₂ ^ 2)
    / (1 - 6 * (τ : ℝ) ^ 2 * K₃ ^ 2)

/-- The left-hand side of (4.4) as a function of `γ`:
`2τγe^{2τγ}(H₁ + τH₂) + γc₂` (with the corrected `H₁`). Theorem 4.2's rate `γ` is the
unique positive root of `rateEquationLHS γ = λ`. -/
noncomputable def rateEquationLHS (K₁ K₂ K₃ lam₁ c₂ : ℝ) (τ : ℝ≥0) (γ : ℝ) : ℝ :=
  2 * τ * γ * Real.exp (2 * τ * γ) * (H1 K₁ K₂ K₃ lam₁ τ + τ * H2 K₁ K₂ K₃ lam₁ τ) + γ * c₂

end You2015.Expo


