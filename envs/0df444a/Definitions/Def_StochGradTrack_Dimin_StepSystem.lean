-- Prove2me | Definitions.Def_StochGradTrack_Dimin_StepSystem
-- name    : StochGradTrack_Dimin_StepSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:55.777555+00:00
-- url     : https://prove2.me/theorems/e83e4f06-9582-4728-8193-cb673c8c7b27
-- title:
--   §2.1 and §3.3, pp. 418, 425 — the stepsize α_k = θ/(m+k), β_k, M_k, the matrix A_k of (29) and the constant C of Theorem 2
-- statement:
--   The scalar and matrix quantities of Theorem 2 and its proof. Throughout, $\theta,m,\mu,L,\sigma,\rho,w$ are real parameters and $n$ is the number of agents; in the theorems $\rho=\rho_w$ and $w=\|\mathbf W-\mathbf I\|$ (Frobenius norm).
--
--   1. The stepsize $\alpha_k=\dfrac{\theta}{m+k}$.
--   2. $M_k=\big[3\alpha_k^2L^2+2(\alpha_kL+1)(n+1)\big]\sigma^2$ (display (30)).
--   3. $\beta_k=\dfrac{1-\rho^2}{2\rho^2}-4\alpha_kL-2\alpha_k^2L^2$.
--   4. The matrix of (29),
--   $$\mathbf A_k=\begin{bmatrix}1-\alpha_k\mu & \frac{\alpha_kL^2}{\mu n}(1+\alpha_k\mu) & 0\\ 0 & \frac12(1+\rho^2) & \alpha_k^2\frac{(1+\rho^2)\rho^2}{1-\rho^2}\\ 2\alpha_k nL^3 & \big(\frac1{\beta_k}+2\big)w^2L^2+3\alpha_kL^3 & \frac12(1+\rho^2)\end{bmatrix},$$
--   and the vector $b_k=(\alpha_k^2\sigma^2/n,\;0,\;M_k)$.
--   5. The constant of Theorem 2,
--   $$C=\Big[\Big(\frac{1-\rho^2}{2\rho^2}-\frac{4\theta L}{m}-\frac{2\theta^2L^2}{m^2}\Big)^{-1}+2\Big]w^2L^2+\frac{3\theta L^3}{m}.$$
--
--   These definitions let the linear system (29) and condition (14) be written as on the page.
--
--   **Formalization Note** $(\cdot)^{-1}$ and $1/\beta_k$ are Lean's real inverse, which is $0$ at $0$; every statement using them assumes the quantity is positive (condition (14) gives $\beta_0>0$ by (31)).
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), Theorem 2 (definition of α_k and C), p. 418; (29), (30) and β_k, §3.3, p. 425

import Mathlib

namespace StochGradTrack.Dimin

/-- The diminishing stepsize `α_k = θ / (m + k)` of Theorem 2. -/
noncomputable def stepDimin (θ m : ℝ) (k : ℕ) : ℝ := θ / (m + k)

/-- `M_k = [3 α_k² L² + 2 (α_k L + 1)(n + 1)] σ²`, display (30). -/
noncomputable def Mk (θ m L : ℝ) (n : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  (3 * stepDimin θ m k ^ 2 * L ^ 2 + 2 * (stepDimin θ m k * L + 1) * (n + 1)) * σ ^ 2

/-- `β_k = (1 − ρ²)/(2ρ²) − 4 α_k L − 2 α_k² L²` (§3.3). -/
noncomputable def betaK (θ m L ρ : ℝ) (k : ℕ) : ℝ :=
  (1 - ρ ^ 2) / (2 * ρ ^ 2) - 4 * stepDimin θ m k * L - 2 * stepDimin θ m k ^ 2 * L ^ 2

/-- The matrix `A_k` of (29); `ρ = ρ_w`, `w = ‖W − I‖` (Frobenius). -/
noncomputable def Ak (θ m μ L : ℝ) (n : ℕ) (ρ w : ℝ) (k : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - stepDimin θ m k * μ, stepDimin θ m k * L ^ 2 / (μ * n) * (1 + stepDimin θ m k * μ), 0;
     0, (1 + ρ ^ 2) / 2, stepDimin θ m k ^ 2 * ((1 + ρ ^ 2) * ρ ^ 2 / (1 - ρ ^ 2));
     2 * stepDimin θ m k * n * L ^ 3,
       (1 / betaK θ m L ρ k + 2) * w ^ 2 * L ^ 2 + 3 * stepDimin θ m k * L ^ 3, (1 + ρ ^ 2) / 2]

/-- The vector `(α_k² σ² / n, 0, M_k)` of (29). -/
noncomputable def bk (θ m L : ℝ) (n : ℕ) (σ : ℝ) (k : ℕ) : Fin 3 → ℝ :=
  ![stepDimin θ m k ^ 2 * σ ^ 2 / n, 0, Mk θ m L n σ k]

/-- The constant `C = [((1 − ρ²)/(2ρ²) − 4θL/m − 2θ²L²/m²)⁻¹ + 2] ‖W − I‖² L² + 3θL³/m` of Theorem 2,
with `w = ‖W − I‖`. -/
noncomputable def Cconst (θ m L ρ w : ℝ) : ℝ :=
  (((1 - ρ ^ 2) / (2 * ρ ^ 2) - 4 * θ * L / m - 2 * θ ^ 2 * L ^ 2 / m ^ 2)⁻¹ + 2) * w ^ 2 * L ^ 2
    + 3 * θ * L ^ 3 / m

end StochGradTrack.Dimin


