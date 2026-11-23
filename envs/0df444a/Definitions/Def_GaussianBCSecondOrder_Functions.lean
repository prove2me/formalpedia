-- Prove2me | Definitions.Def_GaussianBCSecondOrder_Functions
-- name    : GaussianBCSecondOrder_Functions
-- status  : Definition
-- author  : @Vincent Tan
-- created : 2026-11-23T07:26:55.519819+00:00
-- url     : https://prove2.me/theorems/5a890a0e-1a5b-4743-bd68-6e72e4aea3a9
-- title:
--   Gaussian BC second-order region: capacity, dispersion and modified Q-functions
-- statement:
--   This file collects the scalar functions in which the second-order coding region of the scalar Gaussian broadcast channel is expressed. Throughout, $S_1,S_2$ are the signal-to-noise ratios of receivers 1 and 2, $\alpha$ is the power-splitting parameter, $\rho$ is the noise correlation coefficient, and logarithms are natural.
--
--   1. **Capacity and dispersion functions** (eq. (13)):
--   $$\mathsf C(x)=\tfrac12\log(1+x),\qquad \mathsf V(x)=\frac{x(x+2)}{2(x+1)^2},\qquad \mathsf V(x,y)=\frac{x(y+2)}{2(x+1)(y+1)}.$$
--
--   2. **Boundary rates** (eq. (15)): $C_1(\alpha)=\mathsf C(\alpha S_1)$ and $C_2(\alpha)=\mathsf C\big(\tfrac{(1-\alpha)S_2}{1+\alpha S_2}\big)$.
--
--   3. **Supporting weight** (eqs. (17), (18)): $s_j=\alpha+1/S_j$ and $\mu_\alpha=s_2/s_1$.
--
--   4. **Dispersions** (eqs. (20)-(22)):
--   $$V_1(\alpha)=\mathsf V(\alpha S_1),\qquad V_2(\alpha)=\mathsf V(S_2)+\mathsf V(\alpha S_2)-2\mathsf V(\alpha S_2,S_2),$$
--   $$V_{12}(\alpha,\rho)=\rho\Big(\rho-2\sqrt{S_2/S_1}\Big)\big(\mathsf V(\alpha S_1,\alpha S_2)-\mathsf V(\alpha S_1,S_2)\big).$$
--
--   5. **Dispersion matrix and Gaussian functions** (eqs. (23)-(26)): $\Sigma_\alpha(\rho)$ is the symmetric $2\times2$ matrix with diagonal $(V_1(\alpha),V_2(\alpha))$ and off-diagonal entry $V_{12}(\alpha,\rho)$. For $(\mathsf Z_1,\mathsf Z_2)\sim\mathcal N(0,\Sigma_\alpha(\rho))$,
--   $$\Psi_{\alpha,\rho}(z_1,z_2)=\Pr(\mathsf Z_1\le z_1,\mathsf Z_2\le z_2),\qquad \mathsf Q_{\alpha,\rho}(r)=\sup_{z_1+\mu_\alpha z_2=r}\Pr(\mathsf Z_1\ge z_1,\mathsf Z_2\ge z_2),$$
--   and $\mathsf G_{\alpha,\rho}(\varepsilon)=\mathsf Q_{\alpha,\rho}^{-1}(1-\varepsilon)$.
--
--   6. **Standard Gaussian** distribution function $\Phi$ and its inverse $\Phi^{-1}$.
--
--   These are the quantities appearing in Theorem 1 and Proposition 2 of the paper; every statement of the mission shares this single set of definitions.
--
--   **Formalization Note** The law $\mathcal N(0,\Sigma_\alpha(\rho))$ is Mathlib's `multivariateGaussian 0 Σ` on `EuclideanSpace ℝ (Fin 2)`, with coordinate `0` playing the role of $\mathsf Z_1$ and coordinate `1` that of $\mathsf Z_2$ (for a matrix that is not positive semidefinite Mathlib returns a point mass; Proposition 2 asserts positive semidefiniteness for $\alpha\in[0,1]$, $\rho\in[-1,1]$). The inverses $\mathsf Q_{\alpha,\rho}^{-1}$ and $\Phi^{-1}$ are `Function.invFun`: a preimage when one exists and an unspecified real number otherwise; they are only used at arguments in $(0,1)$, where the paper proves a unique preimage exists. The functions are defined for all real arguments and take Lean's default values (e.g. division by zero is zero) outside the parameter ranges of the paper.
-- source:
--   Vincent Y. F. Tan, Second-Order Asymptotics for the Scalar Gaussian Broadcast Channel, arXiv:2611.01583v1 (3 Nov 2026), https://arxiv.org/abs/2611.01583, pp. 6-7, eqs. (13), (15), (17), (18), (20)-(26)

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Function.Basic

/-!
Scalar functions, dispersion matrix and Gaussian functions used to state the second-order
coding region of the scalar Gaussian broadcast channel
(V. Y. F. Tan, arXiv:2611.01583v1, Section II).

Throughout, `S₁ S₂` are the signal-to-noise ratios of receivers 1 and 2, `α` is the
power-splitting parameter and `ρ` is the noise correlation coefficient.
-/

open MeasureTheory ProbabilityTheory

namespace GaussianBCSecondOrder

/-- Gaussian capacity function `C(x) = (1/2) log (1 + x)` (natural logarithm), eq. (13). -/
noncomputable def capacity (x : ℝ) : ℝ := (1 / 2) * Real.log (1 + x)

/-- Gaussian dispersion function `V(x) = x (x + 2) / (2 (x + 1)^2)`, eq. (13). -/
noncomputable def dispersion (x : ℝ) : ℝ := x * (x + 2) / (2 * (x + 1) ^ 2)

/-- Gaussian cross-dispersion function `V(x, y) = x (y + 2) / (2 (x + 1) (y + 1))`, eq. (13). -/
noncomputable def crossDispersion (x y : ℝ) : ℝ := x * (y + 2) / (2 * (x + 1) * (y + 1))

/-- `C₁(α) = C(α S₁)`, eq. (15). -/
noncomputable def C₁ (S₁ α : ℝ) : ℝ := capacity (α * S₁)

/-- `C₂(α) = C((1 - α) S₂ / (1 + α S₂))`, eq. (15). -/
noncomputable def C₂ (S₂ α : ℝ) : ℝ := capacity ((1 - α) * S₂ / (1 + α * S₂))

/-- `s_j = α + ν_j = α + 1 / S_j`, eq. (17): the conditional output variance at a receiver with
signal-to-noise ratio `S`. -/
noncomputable def condVar (S α : ℝ) : ℝ := α + 1 / S

/-- The supporting weight `μ_α = s₂ / s₁`, eq. (18). -/
noncomputable def mu (S₁ S₂ α : ℝ) : ℝ := condVar S₂ α / condVar S₁ α

/-- `V₁(α) = V(α S₁)`, eq. (20). -/
noncomputable def V₁ (S₁ α : ℝ) : ℝ := dispersion (α * S₁)

/-- `V₂(α) = V(S₂) + V(α S₂) - 2 V(α S₂, S₂)`, eq. (21). -/
noncomputable def V₂ (S₂ α : ℝ) : ℝ :=
  dispersion S₂ + dispersion (α * S₂) - 2 * crossDispersion (α * S₂) S₂

/-- `V₁₂(α, ρ) = ρ (ρ - 2 √(S₂ / S₁)) (V(α S₁, α S₂) - V(α S₁, S₂))`, eq. (22). -/
noncomputable def V₁₂ (S₁ S₂ α ρ : ℝ) : ℝ :=
  ρ * (ρ - 2 * Real.sqrt (S₂ / S₁)) *
    (crossDispersion (α * S₁) (α * S₂) - crossDispersion (α * S₁) S₂)

/-- The dispersion matrix `Σ_α(ρ)`, eq. (23). -/
noncomputable def dispersionMatrix (S₁ S₂ α ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![V₁ S₁ α, V₁₂ S₁ S₂ α ρ; V₁₂ S₁ S₂ α ρ, V₂ S₂ α]

/-- The law `N(0, Σ_α(ρ))` of the pair `(Z₁, Z₂)` on `ℝ²`; coordinate `0` is `Z₁` and
coordinate `1` is `Z₂`. -/
noncomputable def dispersionLaw (S₁ S₂ α ρ : ℝ) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  multivariateGaussian 0 (dispersionMatrix S₁ S₂ α ρ)

/-- The bivariate Gaussian distribution function
`Ψ_{α,ρ}(z₁, z₂) = Pr(Z₁ ≤ z₁, Z₂ ≤ z₂)`, eq. (24). -/
noncomputable def Psi (S₁ S₂ α ρ z₁ z₂ : ℝ) : ℝ :=
  (dispersionLaw S₁ S₂ α ρ).real {w | w 0 ≤ z₁ ∧ w 1 ≤ z₂}

/-- The joint upper-tail probability `Pr(Z₁ ≥ z₁, Z₂ ≥ z₂)` for `(Z₁, Z₂) ∼ N(0, Σ_α(ρ))`. -/
noncomputable def upperTail (S₁ S₂ α ρ z₁ z₂ : ℝ) : ℝ :=
  (dispersionLaw S₁ S₂ α ρ).real {w | z₁ ≤ w 0 ∧ z₂ ≤ w 1}

/-- The `(α, ρ)`-modified Q-function, eq. (25):
`Q_{α,ρ}(r) = sup { Pr(Z₁ ≥ z₁, Z₂ ≥ z₂) : z₁ + μ_α z₂ = r }`. -/
noncomputable def Qfun (S₁ S₂ α ρ r : ℝ) : ℝ :=
  sSup ((fun z : ℝ × ℝ => upperTail S₁ S₂ α ρ z.1 z.2) '' {z | z.1 + mu S₁ S₂ α * z.2 = r})

/-- `G_{α,ρ}(ε) = Q_{α,ρ}⁻¹(1 - ε)`, eq. (26): the inverse function of `Q_{α,ρ}` evaluated at
`1 - ε`. -/
noncomputable def Gfun (S₁ S₂ α ρ ε : ℝ) : ℝ :=
  Function.invFun (Qfun S₁ S₂ α ρ) (1 - ε)

/-- The standard Gaussian cumulative distribution function `Φ`. -/
noncomputable def Phi (x : ℝ) : ℝ := (gaussianReal 0 1).real (Set.Iic x)

/-- The inverse `Φ⁻¹` of the standard Gaussian cumulative distribution function. -/
noncomputable def PhiInv (ε : ℝ) : ℝ := Function.invFun Phi ε

end GaussianBCSecondOrder


