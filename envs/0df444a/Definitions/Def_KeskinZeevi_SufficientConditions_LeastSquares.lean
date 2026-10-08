-- Prove2me | Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
-- name    : KeskinZeevi_SufficientConditions_LeastSquares
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T03:45:04.775018+00:00
-- url     : https://prove2.me/theorems/3a5c7628-b1d4-4445-a12c-5944ab50607b
-- title:
--   Empirical Fisher information, information metric J_t, least squares and truncated estimates
-- statement:
--   For prices $p_1, \dots, p_t$ and demands $D_1, \dots, D_t$, define the **empirical Fisher information**
--   $$\mathcal{J}_t = \sum_{s=1}^t \begin{bmatrix} 1 & p_s \\ p_s & p_s^2 \end{bmatrix},$$
--   the average price $\bar p_t = t^{-1}\sum_{s=1}^t p_s$, and the **information metric**
--   $$J_t = \sum_{s=1}^t (p_s - \bar p_t)^2 .$$
--   The **least squares estimate** minimizes $\sum_{s=1}^t (D_s - \alpha - \beta p_s)^2$. In closed form it is
--   $$\hat\theta_t = (\hat\alpha_t, \hat\beta_t)^{\mathsf T} = \mathcal{J}_t^{-1} \Big(\sum_{s=1}^t D_s,\ \sum_{s=1}^t D_s p_s\Big)^{\mathsf T}.$$
--   The **truncated estimate** $\vartheta_t$ is the projection of $\hat\theta_t$ onto $\Theta$. The smallest eigenvalue of a symmetric $2\times 2$ matrix $A$ is written $\mu_{\min}(A) = \inf_{\lVert y \rVert_2 = 1} y^{\mathsf T} A y$, and $\lVert x \rVert_2 = \sqrt{x_1^2 + x_2^2}$ is the Euclidean norm on $\mathbb{R}^2$.
--
--   **Formalization Note.** `fisherOf`, `avgPriceOf`, `infoMetricOf` and `lsEstimateOf` act on arbitrary sequences `ℕ → ℝ`, with sums over $s \in \{1,\dots,t\}$. `fisher`, `infoMetric`, `lsEstimate` and `truncEstimate` are these functions evaluated along the price and demand process of a policy. `minRayleigh` is the infimum of the Rayleigh quotient over unit vectors, which is the smallest eigenvalue by the Rayleigh–Ritz theorem. Two junk values arise. First, $\mathcal{J}_t^{-1}$ is Mathlib's `Matrix.inv`, which is $0$ when $\mathcal{J}_t$ is singular, so $\hat\theta_t = (0,0)$ there. Since $\det \mathcal{J}_t = t J_t$, this happens exactly when $J_t = 0$, and every statement of the mission uses $\hat\theta_t$ only on $\{J_t \ge m\}$ with $m > 0$, or under $J_t \ge \kappa_0\sqrt t > 0$. Second, $\bar p_0 = 0$, which gives $J_0 = 0$.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1145, Eqs. (9)-(11) and the truncated estimate; p. 1147, Section 3.2 (information metric J_t)

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_Policy

open Matrix

namespace KeskinZeevi.SufficientConditions

/-- The empirical Fisher information `𝒥_t = Σ_{s=1}^t [1 p_s; p_s p_s²]` of a price sequence
(Keskin–Zeevi 2014, (11)). -/
def fisherOf (p : ℕ → ℝ) (t : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ s ∈ Finset.Icc 1 t, !![1, p s; p s, p s ^ 2]

/-- The average price `p̄_t = t⁻¹ Σ_{s=1}^t p_s`. -/
noncomputable def avgPriceOf (p : ℕ → ℝ) (t : ℕ) : ℝ :=
  (∑ s ∈ Finset.Icc 1 t, p s) / t

/-- The information metric `J_t = Σ_{s=1}^t (p_s - p̄_t)²` (Keskin–Zeevi 2014, p. 1147). -/
noncomputable def infoMetricOf (p : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 t, (p s - avgPriceOf p t) ^ 2

/-- The smallest eigenvalue of a symmetric `2 × 2` real matrix, written as the minimum of the
Rayleigh quotient `yᵀ A y` over Euclidean unit vectors `y` (Rayleigh–Ritz). -/
noncomputable def minRayleigh (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ⨅ y : {y : Fin 2 → ℝ // y 0 ^ 2 + y 1 ^ 2 = 1}, y.1 ⬝ᵥ (A *ᵥ y.1)

/-- The ordinary least squares estimate `(α̂_t, β̂_t) = 𝒥_t⁻¹ (Σ D_s, Σ D_s p_s)` from prices `p`
and demands `D` of periods `1, …, t` (Keskin–Zeevi 2014, (9)–(11)). When `𝒥_t` is singular
Mathlib's `⁻¹` is `0`, so the value is `(0, 0)`; see the statements for where this matters. -/
noncomputable def lsEstimateOf (p D : ℕ → ℝ) (t : ℕ) : ℝ × ℝ :=
  let v := (fisherOf p t)⁻¹ *ᵥ ![∑ s ∈ Finset.Icc 1 t, D s, ∑ s ∈ Finset.Icc 1 t, D s * p s]
  (v 0, v 1)

/-- Euclidean norm on `ℝ²` (Mathlib's norm on `ℝ × ℝ` is the sup norm). -/
noncomputable def euclidNorm (x : ℝ × ℝ) : ℝ := Real.sqrt (x.1 ^ 2 + x.2 ^ 2)

variable {M : Model} {Ω : Type*}

/-- `𝒥_t` along the price process of `π`. -/
noncomputable def fisher (π : Policy M) (θ : ℝ × ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fisherOf (fun s => price π θ ε s ω) t

/-- `J_t` along the price process of `π`. -/
noncomputable def infoMetric (π : Policy M) (θ : ℝ × ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  infoMetricOf (fun s => price π θ ε s ω) t

/-- The least squares estimate `θ̂_t` computed at the end of period `t` under `π`. -/
noncomputable def lsEstimate (π : Policy M) (θ : ℝ × ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    ℝ × ℝ :=
  lsEstimateOf (fun s => price π θ ε s ω) (fun s => demand π θ ε s ω) t

/-- The truncated estimate `ϑ_t = argmin_{ϑ ∈ Θ} ‖ϑ - θ̂_t‖` (Keskin–Zeevi 2014, p. 1145). -/
noncomputable def truncEstimate (π : Policy M) (θ : ℝ × ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    ℝ × ℝ :=
  M.truncate (lsEstimate π θ ε t ω)

end KeskinZeevi.SufficientConditions


