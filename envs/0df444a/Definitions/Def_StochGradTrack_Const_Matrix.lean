-- Prove2me | Definitions.Def_StochGradTrack_Const_Matrix
-- name    : StochGradTrack_Const_Matrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:34.664353+00:00
-- url     : https://prove2.me/theorems/5a768a33-5d8c-4dae-951b-261b834cf213
-- title:
--   Theorem 1 and (21), pp. 416, 420–421 — M_σ of (10), β, the matrix A of (21) for free β, Theorem 1's printed A, and B = (α²σ²/n, 0, M_σ)
-- statement:
--   This module defines the constants and the $3\times3$ matrix of the linear system that drives the analysis of DSGT with a constant stepsize $\alpha$. Throughout, $\rho=\rho_w$, $w=\|\mathbf W-\mathbf I\|$ (Frobenius), $\mu,L$ are the strong-convexity and smoothness constants, $n$ the number of agents and $\sigma^2$ the noise variance bound.
--
--   1. **$M_\sigma$** ((10)): $M_\sigma=\big[3\alpha^2L^2+2(\alpha L+1)(n+1)\big]\sigma^2$.
--   2. **$\beta$** (Theorem 1): $\beta=\dfrac{1-\rho^2}{2\rho^2}-4\alpha L-2\alpha^2L^2$.
--   3. **The matrix of (21)**, for a free parameter $\beta>0$:
--   $$\mathbf A=\begin{bmatrix}1-\alpha\mu & \frac{\alpha L^2}{\mu n}(1+\alpha\mu) & 0\\ 0 & \frac12(1+\rho^2) & \alpha^2\frac{(1+\rho^2)\rho^2}{1-\rho^2}\\ 2\alpha nL^3 & \left(\frac1\beta+2\right)w^2L^2+3\alpha L^3 & (1+4\alpha L+2\alpha^2L^2+\beta)\rho^2\end{bmatrix}.$$
--   4. **Theorem 1's matrix** $\mathbf A$, as printed on p. 416: the matrix above at Theorem 1's $\beta$, with the $(3,3)$ entry written $\frac12(1+\rho^2)$. For this $\beta$ the two forms of that entry coincide (relation (23)).
--   5. **The vector** $B=\big(\alpha^2\sigma^2/n,\ 0,\ M_\sigma\big)^\top$ of (21)–(22).
--
--   The goal theorem bounds the spectral radius of Theorem 1's $\mathbf A$, and the milestones (21), (22), the $\det(\mathbf I-\mathbf A)$ estimate and Corollary 1 are stated with these objects.
--
--   **Formalization Note.** All arguments are real numbers ($n$ is passed as a real). Entries are indexed from $0$ in Lean: $a_{ij}$ is `A (i-1) (j-1)`. The divisions by $\rho^2$, $1-\rho^2$, $\mu n$ and $\beta$ are total in Lean; every theorem using them assumes $0<\rho<1$, $\mu>0$, $n\ge1$ and $\beta>0$ (or Theorem 1's $\beta$, which is positive under (7) by (27)).
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), Theorem 1 with (10), p. 416; (21) and the entries of A, pp. 420–421; B in §3.1, p. 422

import Mathlib

namespace StochGradTrack.Const

/-- `M_σ := [3α²L² + 2(αL + 1)(n + 1)] σ²` ((10), p. 416). -/
noncomputable def Msigma (α L n σ : ℝ) : ℝ :=
  (3 * α ^ 2 * L ^ 2 + 2 * (α * L + 1) * (n + 1)) * σ ^ 2

/-- Theorem 1's `β = (1 − ρ_w²)/(2ρ_w²) − 4αL − 2α²L²` (p. 416). -/
noncomputable def betaT (α L ρ : ℝ) : ℝ :=
  (1 - ρ ^ 2) / (2 * ρ ^ 2) - 4 * α * L - 2 * α ^ 2 * L ^ 2

/-- The matrix `A = [aᵢⱼ]` of the linear system (21) (pp. 420–421) for a free parameter `β`, with
`ρ = ρ_w` and `w = ‖W − I‖` (Frobenius):
`a₁₁ = 1 − αμ`, `a₁₂ = (αL²/(μn))(1 + αμ)`, `a₁₃ = 0`;
`a₂₁ = 0`, `a₂₂ = (1 + ρ²)/2`, `a₂₃ = α²(1 + ρ²)ρ²/(1 − ρ²)`;
`a₃₁ = 2αnL³`, `a₃₂ = (1/β + 2)w²L² + 3αL³`, `a₃₃ = (1 + 4αL + 2α²L² + β)ρ²`. -/
noncomputable def Agen (α β μ L n ρ w : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - α * μ, α * L ^ 2 / (μ * n) * (1 + α * μ), 0;
     0, (1 + ρ ^ 2) / 2, α ^ 2 * ((1 + ρ ^ 2) * ρ ^ 2 / (1 - ρ ^ 2));
     2 * α * n * L ^ 3, (1 / β + 2) * w ^ 2 * L ^ 2 + 3 * α * L ^ 3,
       (1 + 4 * α * L + 2 * α ^ 2 * L ^ 2 + β) * ρ ^ 2]

/-- The matrix `A` of Theorem 1 as printed on p. 416: `Agen` at `β = betaT α L ρ`, except that the
entry `a₃₃` is written `(1 + ρ²)/2` (which equals `(1 + 4αL + 2α²L² + β)ρ²` for this `β`, (23)). -/
noncomputable def Athm1 (α μ L n ρ w : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - α * μ, α * L ^ 2 / (μ * n) * (1 + α * μ), 0;
     0, (1 + ρ ^ 2) / 2, α ^ 2 * ((1 + ρ ^ 2) * ρ ^ 2 / (1 - ρ ^ 2));
     2 * α * n * L ^ 3, (1 / betaT α L ρ + 2) * w ^ 2 * L ^ 2 + 3 * α * L ^ 3, (1 + ρ ^ 2) / 2]

/-- The constant vector `B = (α²σ²/n, 0, M_σ)ᵀ` of (21)–(22) (pp. 420–422). -/
noncomputable def noiseVec (α L n σ : ℝ) : Fin 3 → ℝ :=
  ![α ^ 2 * σ ^ 2 / n, 0, Msigma α L n σ]

end StochGradTrack.Const


