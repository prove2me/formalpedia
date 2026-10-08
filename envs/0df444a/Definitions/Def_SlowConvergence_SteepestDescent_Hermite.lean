-- Prove2me | Definitions.Def_SlowConvergence_SteepestDescent_Hermite
-- name    : SlowConvergence_SteepestDescent_Hermite
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:32.087595+00:00
-- url     : https://prove2.me/theorems/de41eabc-7acb-4b27-aef5-0d24e0c02ccc
-- title:
--   The quintic Hermite piece $p_k$ (2.11) with coefficients (2.14), and $\psi_k$, $\phi_k$ of (2.15)
-- statement:
--   With the data of (2.5)–(2.10) (iterates $x_k$, steps $s_k$, exponent $\eta = \tau/(4-2\tau)$, step lengths $\alpha_k$), let $\mu_k = s_k = \alpha_k \big(\tfrac{1}{k+1}\big)^{\frac12+\eta}$ be the length of the $k$-th interpolation interval $[0, \mu_k]$, and set
--   $$\psi_k = \Big(\frac{k+1}{k+2}\Big)^{\frac12+\eta}, \qquad \phi_k = \frac{1}{\alpha_k}\big(1 - \alpha_k - \psi_k\big) \qquad (2.15).$$
--   The **Hermite piece** of the example is the quintic polynomial
--   $$p_k(t) = c_{0,k} + c_{1,k}t + c_{2,k}t^2 + c_{3,k}t^3 + c_{4,k}t^4 + c_{5,k}t^5 \qquad (2.11)$$
--   with coefficients
--   $$c_{0,k} = \alpha_k\big(1-\tfrac12\alpha_k\big)\Big(\frac{1}{k+1}\Big)^{1+2\eta}, \quad c_{1,k} = -\Big(\frac{1}{k+1}\Big)^{\frac12+\eta}, \quad c_{2,k} = \frac12,$$
--   $$c_{3,k} = -4\,\frac{\phi_k}{\mu_k}, \qquad c_{4,k} = 7\,\frac{\phi_k}{\mu_k^2}, \qquad c_{5,k} = -3\,\frac{\phi_k}{\mu_k^3} \qquad (2.14).$$
--   The objective of the example is assembled from these pieces by $f_1(x) = p_k(x - x_k) + f_{k+1}$ on $[x_k, x_{k+1}]$ (2.16).
--
--   **Formalization Note** $p_k$ is defined as a polynomial function on all of $\mathbb R$; only its restriction to $[0,\mu_k]$ is used by the example. $\phi_k$ and the coefficients divide by $\alpha_k$ and $\mu_k$, which are positive under the paper's condition (2.6); the milestones assume (2.6).
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 4, §2, (2.11), (2.14), (2.15)

import Mathlib
import Definitions.Def_SlowConvergence_SteepestDescent_Data

namespace SlowConvergence.SteepestDescent

/-- The length `µ_k = s_k = α_k (1/(k+1))^{1/2+η}` of the interpolation interval `[0, µ_k]`, p. 4. -/
noncomputable def mu (τ : ℝ) (α : ℕ → ℝ) (k : ℕ) : ℝ := sk τ α k

/-- `ψ_k = ((k+1)/(k+2))^{1/2+η}` of (2.15), p. 4. -/
noncomputable def psi (τ : ℝ) (k : ℕ) : ℝ := (((k : ℝ) + 1) / ((k : ℝ) + 2)) ^ (1 / 2 + SlowConvergence.Newton.eta τ)

/-- `φ_k = (1/α_k)(1 − α_k − ψ_k)` of (2.15), p. 4. -/
noncomputable def phi (τ : ℝ) (α : ℕ → ℝ) (k : ℕ) : ℝ := 1 / α k * (1 - α k - psi τ k)

/-- The quintic Hermite piece `p_k(t) = c_{0,k} + c_{1,k} t + … + c_{5,k} t⁵` of (2.11), p. 4, with
the coefficients of p. 4 and (2.14):
`c_{0,k} = α_k(1 − ½α_k)(1/(k+1))^{1+2η}`, `c_{1,k} = −(1/(k+1))^{1/2+η}`, `c_{2,k} = ½`,
`c_{3,k} = −4φ_k/µ_k`, `c_{4,k} = 7φ_k/µ_k²`, `c_{5,k} = −3φ_k/µ_k³`.
It is used on `[0, µ_k]`; here it is the polynomial function on all of `ℝ`. -/
noncomputable def p (τ : ℝ) (α : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  α k * (1 - 1 / 2 * α k) * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * SlowConvergence.Newton.eta τ)
    + (-((1 / ((k : ℝ) + 1)) ^ (1 / 2 + SlowConvergence.Newton.eta τ))) * t
    + 1 / 2 * t ^ 2
    + (-4 * phi τ α k / mu τ α k) * t ^ 3
    + (7 * phi τ α k / mu τ α k ^ 2) * t ^ 4
    + (-3 * phi τ α k / mu τ α k ^ 3) * t ^ 5

end SlowConvergence.SteepestDescent


