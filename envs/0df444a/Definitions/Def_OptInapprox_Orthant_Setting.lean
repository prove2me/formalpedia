-- Prove2me | Definitions.Def_OptInapprox_Orthant_Setting
-- name    : OptInapprox_Orthant_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:45.4684+00:00
-- url     : https://prove2.me/theorems/698d0104-9feb-4db4-a57b-6d9e8270acbb
-- title:
--   Definition 8, p. 9; Proposition 6.1, p. 14 — φ, N, the correlated Gaussian orthant probability Λ_ρ(μ), and the exponents g, h of p. 30
-- statement:
--   Let $X$ and $Y$ be independent standard Gaussian random variables, i.e. their joint law is the product $\gamma\otimes\gamma$ of two copies of the standard normal law $\gamma=\mathcal N(0,1)$ on $\mathbb R$. This file fixes the objects of Proposition 6.1 and its proof.
--
--   1. The **Gaussian density** $\phi(x)=\frac{1}{\sqrt{2\pi}}e^{-x^2/2}$.
--   2. The **Gaussian tail probability function**
--   $$N(x)=\int_x^\infty \phi(s)\,ds .$$
--   3. For $\rho\in[-1,1]$ put $X'=\rho X+\sqrt{1-\rho^2}\,Y$. Then $(X,X')$ is a centred normal pair with covariance matrix $\begin{pmatrix}1&\rho\\ \rho&1\end{pmatrix}$. The **orthant probability** at level $t$ is
--   $$\Pr[X\ge t\ \text{and}\ X'\ge t].$$
--   4. For $\mu\in\mathbb R$, **$\Lambda_\rho(\mu)$** is the orthant probability at the level $t$ for which $\Pr[X\ge t]=\mu$ (Definition 8):
--   $$\Lambda_\rho(\mu)=\Pr[X\ge t\ \text{and}\ X'\ge t],\qquad \Pr[X\ge t]=\mu .$$
--   Such a $t$ exists exactly when $0<\mu<1$, and it is then unique because $t\mapsto\Pr[X\ge t]$ is strictly decreasing.
--   5. The two exponents used in the proof of Proposition 6.1 (p. 30): for $u,v\in\mathbb R$,
--   $$g(u,v)=\frac{u+v}{1+\rho}+\frac{(u-v)^2+2(1-\rho)uv}{2(1-\rho^2)t^2},\qquad h(u,v)=\frac{u+v}{1+\rho}+\frac{(u-v)^2}{2(1-\rho^2)t^2}.$$
--
--   $\Lambda_\rho(\mu)$ is the noise stability of a threshold function in Gaussian space; it is the quantity in terms of which the MOO theorem bounds the noise stability of low-influence functions, and its asymptotics drive the MAX-2LIN(q) hardness results of the paper.
--
--   **Formalization Note** $\phi$ is written out explicitly (it equals Mathlib's `gaussianPDFReal 0 1`), and $N(x)$ is the integral over the open ray $(x,\infty)$, which agrees with $[x,\infty)$ for a density. The Gaussian pair is built as Definition 8's pair is represented on p. 31: `stdGaussPair` is the product of two `gaussianReal 0 1` measures on $\mathbb R\times\mathbb R$, and the event is $\{X\ge t,\ \rho X+\sqrt{1-\rho^2}Y\ge t\}$. `Lambda ρ μ` is a genuine probability: it chooses (with `Classical.choose`) a $t$ with $\Pr[X\ge t]=\mu$, where the probability is computed under `gaussianReal 0 1`; for $\mu\notin(0,1)$, where no such $t$ exists, it is the placeholder $0$, which no statement of the mission uses. Definition 8 restricts to $\rho\in[0,1]$; the definitions accept every real $\rho$ and each theorem states the range it needs. The exponents carry $\rho$ and $t$ as explicit arguments; for $\rho=\pm1$ or $t=0$ their denominators vanish, and no statement uses them there.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 9, Definition 8; p. 14, Proposition 6.1; p. 30, proof of Proposition 6.1 (definitions of g and h); p. 31, proof of Proposition 11.3 (X′ = ρX + √(1 − ρ²)Y)

import Mathlib

namespace OptInapprox.Orthant

open MeasureTheory ProbabilityTheory

/-- The standard Gaussian density `φ(x) = (1/√(2π)) e^{-x²/2}` (Proposition 6.1, p. 14). -/
noncomputable def phi (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)

/-- The Gaussian tail probability function `N(x) = ∫_x^∞ φ` (Proposition 6.1, p. 14). -/
noncomputable def tailN (x : ℝ) : ℝ :=
  ∫ s in Set.Ioi x, phi s

/-- The law of a pair `(X, Y)` of independent standard Gaussians on `ℝ × ℝ`. -/
noncomputable def stdGaussPair : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

/-- `Pr[X ≥ t and X' ≥ t]`, where `X` and `Y` are independent standard Gaussians and
`X' = ρ X + √(1 - ρ²) Y` (the representation on p. 31). For `ρ ∈ [-1, 1]` the pair `(X, X')` is a
centred normal vector with covariance matrix `(1 ρ; ρ 1)`, the pair of Definition 8 (p. 9). -/
noncomputable def orthantProb (ρ t : ℝ) : ℝ :=
  (stdGaussPair {p : ℝ × ℝ | t ≤ p.1 ∧ t ≤ ρ * p.1 + Real.sqrt (1 - ρ ^ 2) * p.2}).toReal

open scoped Classical in
/-- `Λ_ρ(μ) = Pr[X ≥ t and X' ≥ t]` where `t` is chosen so that `Pr[X ≥ t] = μ` (Definition 8, p. 9).
Such a `t` exists exactly when `0 < μ < 1`, and it is then unique; for other `μ` the value is the
placeholder `0`. -/
noncomputable def Lambda (ρ μ : ℝ) : ℝ :=
  if h : ∃ t : ℝ, (gaussianReal 0 1 (Set.Ici t)).toReal = μ then
    orthantProb ρ (Classical.choose h)
  else 0

/-- The exponent `g(u, v) = (u + v)/(1 + ρ) + ((u - v)² + 2(1 - ρ)uv) / (2(1 - ρ²)t²)` of (18), p. 30. -/
noncomputable def gExp (ρ t u v : ℝ) : ℝ :=
  (u + v) / (1 + ρ) + ((u - v) ^ 2 + 2 * (1 - ρ) * u * v) / (2 * (1 - ρ ^ 2) * t ^ 2)

/-- The exponent `h(u, v) = (u + v)/(1 + ρ) + (u - v)² / (2(1 - ρ²)t²)` of p. 30. -/
noncomputable def hExp (ρ t u v : ℝ) : ℝ :=
  (u + v) / (1 + ρ) + (u - v) ^ 2 / (2 * (1 - ρ ^ 2) * t ^ 2)

end OptInapprox.Orthant


