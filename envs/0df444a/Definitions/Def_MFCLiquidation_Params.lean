-- Prove2me | Definitions.Def_MFCLiquidation_Params
-- name    : MFCLiquidation_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:23:37.261643+00:00
-- url     : https://prove2.me/theorems/3a0e4d69-1c4c-4ce1-a5b7-35281ebd9865
-- title:
--   Model coefficients, standing assumption (items 1–2), the matrices of (2.19), $\tilde a$, $a$, $I^A$, $I^B$, $I^D$
-- statement:
--   The model has six nonnegative coefficients: the impact parameters $\gamma_1,\gamma_2$, the feedback strength $\alpha$, the decay rate $\beta$ of the child-order flow, the resilience $\rho$ and the risk-aversion parameter $\lambda$. Items 1–2 of the **standing assumption** require
--   $$\gamma_1,\gamma_2,\alpha,\beta,\rho,\lambda\ge0,\qquad \beta-\alpha>0,\qquad \gamma_2\rho-\gamma_1\alpha+\lambda>0 .$$
--
--   With $\tilde a=\gamma_2\rho+\lambda$ and $a=\gamma_2\rho-\gamma_1\alpha+\lambda$, the state $\mathcal X=(X,Y,C)$ (inventory, price impact, expected child-order flow) has the coefficients of (2.19):
--   $$\mathcal H=\begin{pmatrix}0&0&0\\0&-\rho&-\gamma_1(\beta-\alpha)\\0&0&-(\beta-\alpha)\end{pmatrix},\quad \overline{\mathcal H}=\begin{pmatrix}0&0&0\\-\alpha\gamma_1&0&0\\-\alpha&0&0\end{pmatrix},\quad \mathcal G=\begin{pmatrix}0\\\alpha\gamma_1\mathbb E[x_0]\\\alpha\mathbb E[x_0]\end{pmatrix},\quad \mathcal K=\begin{pmatrix}-1\\\gamma_2\\0\end{pmatrix},$$
--   and $\mathcal Q=\operatorname{diag}(\lambda,0,0)$.
--
--   The coefficient matrices $A,B$ are symmetric with $x_{11}=\gamma_2x_{21}$, $x_{12}=\gamma_2x_{22}+\tfrac12$, $x_{13}=\gamma_2x_{23}$, so each is determined by $(x_{11},x_{13},x_{33})$; the vector $D$ has $D_2=\gamma_2^{-1}D_1$. The feedback vectors are
--   $$I^A=\Big(-\rho A_{11}-\lambda,\ -\rho\tfrac{A_{11}}{\gamma_2}+\rho,\ \tfrac{\gamma_1(\beta-\alpha)}2-\rho A_{13}\Big),$$
--   $$I^B=\Big(\tfrac{\alpha\gamma_1-\gamma_2\rho}{\gamma_2}B_{11}+\alpha B_{13}-\lambda+\tfrac{\alpha\gamma_1}2,\ \tfrac{\alpha\gamma_1-\gamma_2\rho}{\gamma_2^2}B_{11}+\alpha\tfrac{B_{13}}{\gamma_2}+\rho-\tfrac{\alpha\gamma_1}{2\gamma_2},\ \tfrac{\gamma_1(\beta-\alpha)}2+(\gamma_1\alpha-\gamma_2\rho)\tfrac{B_{13}}{\gamma_2}+\alpha B_{33}\Big),$$
--   $$I^D=-\tfrac{\alpha\gamma_1}2\mathbb E[x_0]+(\gamma_1\alpha-\gamma_2\rho)\tfrac{D_1}{2\gamma_2}+\tfrac\alpha2D_3 .$$
--
--   These are the algebraic building blocks of every statement of the mission.
--
--   **Formalization Note** `lam` is $\lambda$ (a Lean keyword). The relations are solved for the second row, which divides by $\gamma_2$; every formula of the paper divides by $\gamma_2$. `symMatDot` is the derivative of `symMat` (the constant $\tfrac12$ drops). The horizon $T$ is not a coefficient, so that the threshold on $\alpha$ can be chosen before it.
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, standing assumption items 1–2, p.10; (2.19) and the formulas for ã, a, I^A, I^B, I^D, p.11; the relations above (2.14) and (2.15), p.9; 𝒬 = diag(λ, 0, 0), p.19

import Mathlib

open Matrix

namespace MFCLiquidation

/-- The model coefficients `γ₁, γ₂, α, β, ρ, λ` of Fu, Horst & Xia, arXiv:2207.00446v3, (2.10) and
(2.9), p.8. The horizon `T` is not a coefficient: it is part of the probabilistic data, so that the
threshold on `α` in Theorems 2.3 and 3.1 can be chosen independently of it.

Formalization Note: `lam` is the paper's `λ`, a reserved word in Lean. -/
structure Params where
  γ₁ : ℝ
  γ₂ : ℝ
  α : ℝ
  β : ℝ
  ρ : ℝ
  lam : ℝ

namespace Params

/-- Items 1 and 2 of the standing assumption, arXiv:2207.00446v3, p.10: the six coefficients are
nonnegative, `β − α > 0` and `γ₂ρ − γ₁α + λ > 0`. Item 3 concerns the random data and is
`Model.Assumption`. -/
def Standing (p : Params) : Prop :=
  0 ≤ p.γ₁ ∧ 0 ≤ p.γ₂ ∧ 0 ≤ p.α ∧ 0 ≤ p.β ∧ 0 ≤ p.ρ ∧ 0 ≤ p.lam ∧
    0 < p.β - p.α ∧ 0 < p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam

/-- `ã = γ₂ρ + λ`, arXiv:2207.00446v3, p.11. -/
noncomputable def aTilde (p : Params) : ℝ := p.γ₂ * p.ρ + p.lam

/-- `a = γ₂ρ − γ₁α + λ`, arXiv:2207.00446v3, p.11. -/
noncomputable def a (p : Params) : ℝ := p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam

/-- The matrix `ℋ` of (2.19), arXiv:2207.00446v3, p.11. Components are ordered `(X, Y, C)`. -/
noncomputable def H (p : Params) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0;
     0, -p.ρ, -(p.γ₁ * (p.β - p.α));
     0, 0, -(p.β - p.α)]

/-- The matrix `ℋ̄` of (2.19), arXiv:2207.00446v3, p.11. -/
noncomputable def Hbar (p : Params) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0;
     -(p.α * p.γ₁), 0, 0;
     -p.α, 0, 0]

/-- The vector `𝒢 = (0, αγ₁E[x₀], αE[x₀])ᵀ` of (2.19), arXiv:2207.00446v3, p.11. `Ex0` is `E[x₀]`,
the time-0 mean inventory: a model constant at every initial time `t`. -/
noncomputable def G (p : Params) (Ex0 : ℝ) : Fin 3 → ℝ :=
  ![0, p.α * p.γ₁ * Ex0, p.α * Ex0]

/-- The vector `𝒦 = (−1, γ₂, 0)ᵀ` of (2.19), arXiv:2207.00446v3, p.11. -/
noncomputable def K (p : Params) : Fin 3 → ℝ := ![-1, p.γ₂, 0]

/-- The matrix `𝒬 = diag(λ, 0, 0)`, arXiv:2207.00446v3, p.19. -/
noncomputable def Q (p : Params) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![p.lam, 0, 0]

/-- The symmetric `3 × 3` matrix with free entries `x₁₁, x₁₃, x₃₃` and the entries forced by the
relations stated above (2.14) and above (2.15), arXiv:2207.00446v3, p.9:
`x₁₁ = γ₂x₂₁`, `x₁₂ = γ₂x₂₂ + ½`, `x₁₃ = γ₂x₂₃`. Both `A` and `B` have this form.

Formalization Note: the relations are solved for `x₂₁`, `x₂₂`, `x₂₃`; this divides by `γ₂`, which
is positive wherever the paper's formulas (all of which divide by `γ₂`) make sense. -/
noncomputable def symMat (p : Params) (x₁₁ x₁₃ x₃₃ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![x₁₁, x₁₁ / p.γ₂, x₁₃;
     x₁₁ / p.γ₂, (x₁₁ / p.γ₂ - 1 / 2) / p.γ₂, x₁₃ / p.γ₂;
     x₁₃, x₁₃ / p.γ₂, x₃₃]

/-- The time derivative of `symMat`, given the derivatives `y₁₁, y₁₃, y₃₃` of the free entries:
differentiating the relations above (2.14) kills the constant `½`. -/
noncomputable def symMatDot (p : Params) (y₁₁ y₁₃ y₃₃ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![y₁₁, y₁₁ / p.γ₂, y₁₃;
     y₁₁ / p.γ₂, y₁₁ / p.γ₂ / p.γ₂, y₁₃ / p.γ₂;
     y₁₃, y₁₃ / p.γ₂, y₃₃]

/-- The vector `D = (D₁, D₂, D₃)` with `D₂ = γ₂⁻¹D₁`, arXiv:2207.00446v3, p.9. -/
noncomputable def dVec (p : Params) (d₁ d₃ : ℝ) : Fin 3 → ℝ := ![d₁, d₁ / p.γ₂, d₃]

/-- The row vector `I^A` of arXiv:2207.00446v3, p.11, as a function of `A₁₁, A₁₃`. -/
noncomputable def IA (p : Params) (a₁₁ a₁₃ : ℝ) : Fin 3 → ℝ :=
  ![-p.ρ * a₁₁ - p.lam,
    -p.ρ * (a₁₁ / p.γ₂) + p.ρ,
    p.γ₁ * (p.β - p.α) / 2 - p.ρ * a₁₃]

/-- The row vector `I^B` of arXiv:2207.00446v3, p.11, as a function of `B₁₁, B₁₃, B₃₃`. -/
noncomputable def IB (p : Params) (b₁₁ b₁₃ b₃₃ : ℝ) : Fin 3 → ℝ :=
  ![(p.α * p.γ₁ - p.γ₂ * p.ρ) / p.γ₂ * b₁₁ + p.α * b₁₃ - p.lam + p.α * p.γ₁ / 2,
    (p.α * p.γ₁ - p.γ₂ * p.ρ) / p.γ₂ ^ 2 * b₁₁ + p.α * (b₁₃ / p.γ₂) + p.ρ
      - p.α * p.γ₁ / (2 * p.γ₂),
    p.γ₁ * (p.β - p.α) / 2 + (p.γ₁ * p.α - p.γ₂ * p.ρ) * (b₁₃ / p.γ₂) + p.α * b₃₃]

/-- The scalar `I^D` of arXiv:2207.00446v3, p.11, as a function of `E[x₀], D₁, D₃`. -/
noncomputable def ID (p : Params) (Ex0 d₁ d₃ : ℝ) : ℝ :=
  -(p.α * p.γ₁ / 2) * Ex0 + (p.γ₁ * p.α - p.γ₂ * p.ρ) * (d₁ / (2 * p.γ₂)) + p.α / 2 * d₃

end Params

end MFCLiquidation


