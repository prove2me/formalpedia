-- Prove2me | Definitions.Def_SpikedWishart_Separated_Phase
-- name    : SpikedWishart_Separated_Phase
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:35:50.551747+00:00
-- url     : https://prove2.me/theorems/88082a12-2fee-4e41-8800-79410007610c
-- title:
--   §4, pp. 1678–1685, (211), (215)–(216), (220), (262) — μ, ν, the phase f, the factor g, q, π_*, and x₀, θ₀
-- statement:
--   This file defines the quantities of the steepest-descent analysis of §4. Throughout, $\gamma \ge 1$, $\pi_1 = \ell_1^{-1}$, and $\pi_{k+1},\dots,\pi_r$ are the inverses of the remaining non-unit population eigenvalues.
--
--   1. (211): $\mu = \dfrac1{\pi_1} + \dfrac{\gamma^{-2}}{1-\pi_1}$ and $\nu = \sqrt{\dfrac1{\pi_1^2} - \dfrac{\gamma^{-2}}{(1-\pi_1)^2}}$.
--   2. (220): for $\varepsilon > 0$ and a sample size $M$, $q = \pi_1 - \dfrac{\varepsilon}{\nu\sqrt M}$.
--   3. (215): the **phase function**, with $\log$ the principal branch,
--   $$
--   f(z) = -\mu(z-q) + \log z - \frac1{\gamma^2}\log(1-z).
--   $$
--   4. (216): with $r = k + m$, $g(z) = (1-z)^{-r}\prod_{\ell=k+1}^r(\pi_\ell - z)$.
--   5. p. 1685: $\pi_* = \min\{\pi_{k+1},\dots,\pi_r, 1, 1/(\mu\pi_1)\}$.
--   6. (262): for $0 < \delta < 1/(1+\gamma)$, $x_0$ and $\theta_0 \in (0, \pi/2)$ are defined by $x_0 + i\delta = 1 + \frac1{1+\gamma}e^{i(\pi-\theta_0)}$, that is $\sin\theta_0 = \delta(1+\gamma)$ and $x_0 = 1 - \sqrt{(1+\gamma)^{-2} - \delta^2}$.
--
--   These are the ingredients of the contour estimates (Lemmas 4.1 and 4.2) and of the kernels of Proposition 4.1.
--
--   **Formalization Note** $\gamma^{-2}$ is written $(\gamma^{-1})^2$. The list $\pi_{k+1},\dots,\pi_r$ is a vector $\pi^o$ of length $m = r - k$, and $\pi_*$ is computed as a fold of $\min$ starting from $\min\{1, 1/(\mu\pi_1)\}$, so it is correct also when $m = 0$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1678, (211), (215), (216); p. 1679, (220); p. 1685, π_* and (262)

import Mathlib

namespace SpikedWishart.Separated

/-- (211): `μ(γ) = 1/π₁ + γ^{−2}/(1 − π₁)`. -/
noncomputable def mu (γ π₁ : ℝ) : ℝ :=
  1 / π₁ + γ⁻¹ ^ 2 / (1 - π₁)

/-- (211): `ν(γ) = √(1/π₁² − γ^{−2}/(1 − π₁)²)`. -/
noncomputable def nu (γ π₁ : ℝ) : ℝ :=
  Real.sqrt (1 / π₁ ^ 2 - γ⁻¹ ^ 2 / (1 - π₁) ^ 2)

/-- (220): `q = π₁ − ε/(ν√M)`. -/
noncomputable def qM (ε γ π₁ : ℝ) (M : ℕ) : ℝ :=
  π₁ - ε / (nu γ π₁ * Real.sqrt M)

/-- (215): the phase `f(z) = −μ(z − q) + log z − γ^{−2} log(1 − z)`, `log` the principal
branch, with `μ = μ(γ)` of (211). -/
noncomputable def fPhase (γ π₁ q : ℝ) (z : ℂ) : ℂ :=
  -((mu γ π₁ : ℝ) : ℂ) * (z - q) + Complex.log z - ((γ⁻¹ ^ 2 : ℝ) : ℂ) * Complex.log (1 - z)

/-- (216): `g(z) = (1 − z)^{−r} Π_{ℓ=k+1}^{r} (π_ℓ − z)`, with `r = k + m` and
`πo : Fin m → ℝ` listing `π_{k+1}, …, π_r`. -/
noncomputable def gFac (k : ℕ) {m : ℕ} (πo : Fin m → ℝ) (z : ℂ) : ℂ :=
  (1 / (1 - z) ^ (k + m)) * ∏ j, ((πo j : ℂ) - z)

/-- p. 1685: `π_* = min{π_{k+1}, …, π_r, 1, 1/(μπ₁)}`. -/
noncomputable def piStar (γ π₁ : ℝ) {m : ℕ} (πo : Fin m → ℝ) : ℝ :=
  (List.ofFn πo).foldr min (min 1 (1 / (mu γ π₁ * π₁)))

/-- (262): the real part `x₀` of `x₀ + iδ = 1 + (1+γ)^{−1} e^{i(π−θ₀)}`,
i.e. `x₀ = 1 − √((1+γ)^{−2} − δ²)` (for `0 < δ ≤ 1/(1+γ)`). -/
noncomputable def gX0 (γ δ : ℝ) : ℝ :=
  1 - Real.sqrt (1 / (1 + γ) ^ 2 - δ ^ 2)

/-- (262): the angle `θ₀ ∈ (0, π/2]` with `sin θ₀ = δ(1+γ)`. -/
noncomputable def theta0 (γ δ : ℝ) : ℝ :=
  Real.arcsin (δ * (1 + γ))

end SpikedWishart.Separated


