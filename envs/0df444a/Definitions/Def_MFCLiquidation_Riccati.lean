-- Prove2me | Definitions.Def_MFCLiquidation_Riccati
-- name    : MFCLiquidation_Riccati
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:24:26.717975+00:00
-- url     : https://prove2.me/theorems/f33ab5fb-00eb-4447-8895-3186b36f5881
-- title:
--   The coefficient ODEs (2.14)–(2.16), the BSDE driver of (2.17), and the matrix Riccati form (3.1)–(3.2)
-- statement:
--   The value function is expressed through deterministic coefficients solving backward ODEs on $[0,T]$.
--
--   1. $(A_{11},A_{13},A_{33})$ solves (2.14): $\dot A_{11}=-\lambda+\frac{(\rho A_{11}+\lambda)^2}{\gamma_2\rho+\lambda}$, $\dot A_{13}=\frac{\gamma_1(\beta-\alpha)}{\gamma_2}A_{11}+(\beta-\alpha)A_{13}-\frac{(\rho A_{11}+\lambda)(\gamma_1(\beta-\alpha)-2\rho A_{13})}{2(\gamma_2\rho+\lambda)}$, $\dot A_{33}=2(\beta-\alpha)A_{33}+2\frac{\gamma_1(\beta-\alpha)}{\gamma_2}A_{13}+\frac{(\gamma_1(\beta-\alpha)-2\rho A_{13})^2}{4(\gamma_2\rho+\lambda)}$, with $A_{11,T}=\gamma_2/2$, $A_{13,T}=A_{33,T}=0$.
--   2. $(B_{11},B_{13},B_{33})$ solves the coupled Riccati system (2.15), with $X_1=2(\gamma_1\alpha-\gamma_2\rho)B_{11}+\gamma_1\gamma_2\alpha+2\alpha\gamma_2B_{13}-2\gamma_2\lambda$, $X_3=2(\gamma_1\alpha-\gamma_2\rho)B_{13}+2\gamma_2\alpha B_{33}+\gamma_1\gamma_2(\beta-\alpha)$ and $d=4\gamma_2^2(\gamma_2\rho-\gamma_1\alpha+\lambda)$: $\dot B_{11}=2\frac{\gamma_1\alpha}{\gamma_2}B_{11}+2\alpha B_{13}-\lambda+X_1^2/d$, $\dot B_{33}=2(\beta-\alpha)B_{33}+2\frac{\gamma_1(\beta-\alpha)}{\gamma_2}B_{13}+X_3^2/d$, $\dot B_{13}=\frac{\gamma_1(\beta-\alpha)}{\gamma_2}B_{11}+\alpha B_{33}+(\beta-\alpha+\frac{\gamma_1\alpha}{\gamma_2})B_{13}+X_1X_3/d$, with $B_{11,T}=\gamma_2/2$, $B_{13,T}=B_{33,T}=0$.
--   3. $(D_1,D_3)$ solves the linear system (2.16) driven by $B$, with $\mathcal Y=-\gamma_1\gamma_2\alpha\mathbb E[x_0]+(\gamma_1\alpha-\gamma_2\rho)D_1+\alpha\gamma_2D_3$: $\dot D_1=-\frac{2\gamma_1\alpha\mathbb E[x_0]}{\gamma_2}B_{11}-2\alpha\mathbb E[x_0]B_{13}+\frac{\gamma_1\alpha}{\gamma_2}D_1+\alpha D_3+\frac{X_1\mathcal Y}{2\gamma_2^2(\gamma_2\rho-\gamma_1\alpha+\lambda)}$ and $\dot D_3=-2\alpha\mathbb E[x_0]B_{33}-\frac{2\gamma_1\alpha\mathbb E[x_0]}{\gamma_2}B_{13}+\frac{\gamma_1(\beta-\alpha)}{\gamma_2}D_1+(\beta-\alpha)D_3+\frac{X_3\mathcal Y}{2\gamma_2^2(\gamma_2\rho-\gamma_1\alpha+\lambda)}$, with $D_{1,T}=D_{3,T}=0$.
--   4. The driver of the BSDE (2.17), $-dF=g\,dt-Z^F\,dW$: $g=\sigma^2\frac{2A_{11}-\gamma_2}{2\gamma_2^2}+\alpha\gamma_1\mathbb E[x_0]\frac{D_1}{\gamma_2}+\alpha\mathbb E[x_0]D_3-\frac{1}{4(\lambda+\gamma_2\rho-\alpha\gamma_1)}\big(-\alpha\gamma_1\mathbb E[x_0]+(\gamma_1\alpha-\gamma_2\rho)\frac{D_1}{\gamma_2}+\alpha D_3\big)^2$.
--   5. The matrices of p.12: $\mathcal N_1$, $\mathcal N_2=(\gamma_1\alpha-\gamma_2\rho,\gamma_2\alpha)^\top$, $\mathcal N_0=1/(\gamma_2^2(\gamma_2\rho-\gamma_1\alpha+\lambda))$, $\mathcal M$, the terminal matrix $\operatorname{diag}(\gamma_2/2,0)$, $\tilde\Lambda=\Lambda\begin{pmatrix}\alpha^2&\alpha(\beta-\alpha)\\\alpha(\beta-\alpha)&(\beta-\alpha)^2\end{pmatrix}$, $\tilde{\mathcal N}_1=\mathcal N_1-\tilde\Lambda\mathcal N_2\mathcal N_0\mathcal N_2^\top$, $\tilde{\mathcal M}=-\tilde\Lambda\mathcal N_2\mathcal N_0\mathcal N_2^\top\tilde\Lambda+\mathcal N_1\tilde\Lambda+\tilde\Lambda\mathcal N_1^\top+\mathcal M$; and the predicate that $P$ solves $\dot P=PSP+NP+PN^\top-Q$ on $[0,T]$ with $P_T=G$.
--
--   **Formalization Note** A solution of an ODE is a function with derivative within $[0,T]$ (one-sided at the endpoints) equal to the right side at every point of $[0,T]$. Two coefficients are corrected against the page: in (2.16) the $B_{13}$ term of the second bracket of $\dot D_1$ is $2\alpha\gamma_2B_{13}$ (the page prints $\alpha\gamma_2B_{13}$; the identity of p.20 on which Proposition 4.1 rests needs the $2$), and the terminal matrix of (3.1) is $\operatorname{diag}(\gamma_2/2,0)$ (the page prints $\gamma_2$, contradicting $B_{11,T}=\gamma_2/2$ in (2.15) and the terminal value $\gamma_2/2+\Lambda\alpha^2$ on p.15).
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, (2.14) and (2.15), p.9; (2.16) and (2.17), p.10; 𝒫, 𝒩₁, 𝒩₂, 𝒩₀, ℳ, 𝒢, Λ̃, 𝒩̃₁, ℳ̃ and (3.1)–(3.2), p.12

import Mathlib
import Definitions.Def_MFCLiquidation_Params

open Matrix Set

namespace MFCLiquidation

namespace Params

/-- Right side of `Ȧ₁₁` in (2.14), arXiv:2207.00446v3, p.9. -/
noncomputable def rhsA₁₁ (p : Params) (a₁₁ : ℝ) : ℝ :=
  -p.lam + (p.ρ * a₁₁ + p.lam) ^ 2 / (p.γ₂ * p.ρ + p.lam)

/-- Right side of `Ȧ₁₃` in (2.14), arXiv:2207.00446v3, p.9. -/
noncomputable def rhsA₁₃ (p : Params) (a₁₁ a₁₃ : ℝ) : ℝ :=
  p.γ₁ * (p.β - p.α) / p.γ₂ * a₁₁ + (p.β - p.α) * a₁₃
    - (p.ρ * a₁₁ + p.lam) * (p.γ₁ * (p.β - p.α) - 2 * p.ρ * a₁₃) / (2 * (p.γ₂ * p.ρ + p.lam))

/-- Right side of `Ȧ₃₃` in (2.14), arXiv:2207.00446v3, p.9. -/
noncomputable def rhsA₃₃ (p : Params) (a₁₃ a₃₃ : ℝ) : ℝ :=
  2 * (p.β - p.α) * a₃₃ + 2 * (p.γ₁ * (p.β - p.α) / p.γ₂) * a₁₃
    + (p.γ₁ * (p.β - p.α) - 2 * p.ρ * a₁₃) ^ 2 / (4 * (p.γ₂ * p.ρ + p.lam))

/-- `(2(γ₁α − γ₂ρ)B₁₁ + γ₁γ₂α + 2αγ₂B₁₃ − 2γ₂λ)`, the first bracket of (2.15),
arXiv:2207.00446v3, p.9. -/
noncomputable def bX₁ (p : Params) (b₁₁ b₁₃ : ℝ) : ℝ :=
  2 * (p.γ₁ * p.α - p.γ₂ * p.ρ) * b₁₁ + p.γ₁ * p.γ₂ * p.α + 2 * p.α * p.γ₂ * b₁₃
    - 2 * p.γ₂ * p.lam

/-- `(2(γ₁α − γ₂ρ)B₁₃ + 2γ₂αB₃₃ + γ₁γ₂(β − α))`, the second bracket of (2.15),
arXiv:2207.00446v3, p.9. -/
noncomputable def bX₃ (p : Params) (b₁₃ b₃₃ : ℝ) : ℝ :=
  2 * (p.γ₁ * p.α - p.γ₂ * p.ρ) * b₁₃ + 2 * p.γ₂ * p.α * b₃₃ + p.γ₁ * p.γ₂ * (p.β - p.α)

/-- Right side of `Ḃ₁₁` in (2.15), arXiv:2207.00446v3, p.9. -/
noncomputable def rhsB₁₁ (p : Params) (b₁₁ b₁₃ : ℝ) : ℝ :=
  2 * (p.γ₁ * p.α / p.γ₂) * b₁₁ + 2 * p.α * b₁₃ - p.lam
    + p.bX₁ b₁₁ b₁₃ ^ 2 / (4 * p.γ₂ ^ 2 * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam))

/-- Right side of `Ḃ₃₃` in (2.15), arXiv:2207.00446v3, p.9. -/
noncomputable def rhsB₃₃ (p : Params) (b₁₃ b₃₃ : ℝ) : ℝ :=
  2 * (p.β - p.α) * b₃₃ + 2 * (p.γ₁ * (p.β - p.α) / p.γ₂) * b₁₃
    + p.bX₃ b₁₃ b₃₃ ^ 2 / (4 * p.γ₂ ^ 2 * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam))

/-- Right side of `Ḃ₁₃` in (2.15), arXiv:2207.00446v3, p.9. -/
noncomputable def rhsB₁₃ (p : Params) (b₁₁ b₁₃ b₃₃ : ℝ) : ℝ :=
  p.γ₁ * (p.β - p.α) / p.γ₂ * b₁₁ + p.α * b₃₃ + (p.β - p.α + p.γ₁ * p.α / p.γ₂) * b₁₃
    + p.bX₁ b₁₁ b₁₃ * p.bX₃ b₁₃ b₃₃ / (4 * p.γ₂ ^ 2 * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam))

/-- `(−γ₁γ₂αE[x₀] + (γ₁α − γ₂ρ)D₁ + αγ₂D₃)`, the common numerator of (2.16),
arXiv:2207.00446v3, p.10. -/
noncomputable def dY (p : Params) (Ex0 d₁ d₃ : ℝ) : ℝ :=
  -(p.γ₁ * p.γ₂ * p.α * Ex0) + (p.γ₁ * p.α - p.γ₂ * p.ρ) * d₁ + p.α * p.γ₂ * d₃

/-- Right side of `Ḋ₁` in (2.16), arXiv:2207.00446v3, p.10, **corrected**: the page prints the
second bracket with `αγ₂B₁₃`; this definition has `2αγ₂B₁₃`, i.e. the bracket `bX₁` of (2.15). The
identity `2I^DI^B/a = 2𝒢ᵀB + Ḋᵀ + Dᵀℋ + Dᵀℋ̄` on p.20, on which Proposition 4.1 rests, holds with
the coefficient `2` and fails with the printed one. -/
noncomputable def rhsD₁ (p : Params) (Ex0 b₁₁ b₁₃ d₁ d₃ : ℝ) : ℝ :=
  -(2 * p.γ₁ * p.α * Ex0 / p.γ₂) * b₁₁ - 2 * p.α * Ex0 * b₁₃ + p.γ₁ * p.α / p.γ₂ * d₁ + p.α * d₃
    + p.bX₁ b₁₁ b₁₃ * p.dY Ex0 d₁ d₃ / (2 * p.γ₂ ^ 2 * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam))

/-- Right side of `Ḋ₃` in (2.16), arXiv:2207.00446v3, p.10. -/
noncomputable def rhsD₃ (p : Params) (Ex0 b₁₃ b₃₃ d₁ d₃ : ℝ) : ℝ :=
  -(2 * p.α * Ex0) * b₃₃ - 2 * p.γ₁ * p.α * Ex0 / p.γ₂ * b₁₃
    + p.γ₁ * (p.β - p.α) / p.γ₂ * d₁ + (p.β - p.α) * d₃
    + p.bX₃ b₁₃ b₃₃ * p.dY Ex0 d₁ d₃ / (2 * p.γ₂ ^ 2 * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam))

/-- `(A₁₁, A₁₃, A₃₃)` solves (2.14), arXiv:2207.00446v3, p.9, on `[0, T]`.

Formalization Note: a solution is a function with a one-sided derivative at the endpoints and the
two-sided one in between, equal to the right side everywhere on the closed interval; since the
right side is continuous along a solution, this is the same as being `C¹` on `[0, T]`, and it is
what the paper's `t ∈ [0, T)` with a terminal value means. -/
def SolvesA (p : Params) (T : ℝ) (A₁₁ A₁₃ A₃₃ : ℝ → ℝ) : Prop :=
  (∀ s ∈ Icc 0 T,
    HasDerivWithinAt A₁₁ (p.rhsA₁₁ (A₁₁ s)) (Icc 0 T) s ∧
    HasDerivWithinAt A₁₃ (p.rhsA₁₃ (A₁₁ s) (A₁₃ s)) (Icc 0 T) s ∧
    HasDerivWithinAt A₃₃ (p.rhsA₃₃ (A₁₃ s) (A₃₃ s)) (Icc 0 T) s) ∧
  A₁₁ T = p.γ₂ / 2 ∧ A₁₃ T = 0 ∧ A₃₃ T = 0

/-- `(B₁₁, B₁₃, B₃₃)` solves (2.15), arXiv:2207.00446v3, p.9, on `[0, T]`, in the sense of
`SolvesA`. -/
def SolvesB (p : Params) (T : ℝ) (B₁₁ B₁₃ B₃₃ : ℝ → ℝ) : Prop :=
  (∀ s ∈ Icc 0 T,
    HasDerivWithinAt B₁₁ (p.rhsB₁₁ (B₁₁ s) (B₁₃ s)) (Icc 0 T) s ∧
    HasDerivWithinAt B₁₃ (p.rhsB₁₃ (B₁₁ s) (B₁₃ s) (B₃₃ s)) (Icc 0 T) s ∧
    HasDerivWithinAt B₃₃ (p.rhsB₃₃ (B₁₃ s) (B₃₃ s)) (Icc 0 T) s) ∧
  B₁₁ T = p.γ₂ / 2 ∧ B₁₃ T = 0 ∧ B₃₃ T = 0

/-- `(D₁, D₃)` solves the corrected (2.16), arXiv:2207.00446v3, p.10, on `[0, T]` for the
coefficient functions `B₁₁, B₁₃, B₃₃`, in the sense of `SolvesA`; `Ex0` is `E[x₀]`. -/
def SolvesD (p : Params) (T Ex0 : ℝ) (B₁₁ B₁₃ B₃₃ D₁ D₃ : ℝ → ℝ) : Prop :=
  (∀ s ∈ Icc 0 T,
    HasDerivWithinAt D₁ (p.rhsD₁ Ex0 (B₁₁ s) (B₁₃ s) (D₁ s) (D₃ s)) (Icc 0 T) s ∧
    HasDerivWithinAt D₃ (p.rhsD₃ Ex0 (B₁₃ s) (B₃₃ s) (D₁ s) (D₃ s)) (Icc 0 T) s) ∧
  D₁ T = 0 ∧ D₃ T = 0

/-- The generator `g` of the BSDE (2.17), arXiv:2207.00446v3, p.10, at a point: `−dF = g dt − Z^F dW`,
with `sg` the volatility `σ_t`, and `a₁₁, d₁, d₃` the coefficients at time `t`. -/
noncomputable def genF (p : Params) (Ex0 sg a₁₁ d₁ d₃ : ℝ) : ℝ :=
  sg ^ 2 * ((2 * a₁₁ - p.γ₂) / (2 * p.γ₂ ^ 2)) + p.α * p.γ₁ * Ex0 * (d₁ / p.γ₂)
    + p.α * Ex0 * d₃
    - 1 / (4 * (p.lam + p.γ₂ * p.ρ - p.α * p.γ₁))
      * (-(p.α * p.γ₁ * Ex0) + (p.γ₁ * p.α - p.γ₂ * p.ρ) * (d₁ / p.γ₂) + p.α * d₃) ^ 2

/-- The matrix `𝒩₁` of arXiv:2207.00446v3, p.12. -/
noncomputable def N₁ (p : Params) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.γ₁ * p.α / p.γ₂
      + (p.γ₁ * p.α - p.γ₂ * p.ρ) * (p.γ₁ * p.α - 2 * p.lam)
        / (2 * p.γ₂ * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam)),
     p.α + p.α * (p.γ₁ * p.α - 2 * p.lam) / (2 * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam));
     p.γ₁ * (p.β - p.α) / p.γ₂
      + (p.γ₁ * p.α - p.γ₂ * p.ρ) * p.γ₁ * (p.β - p.α)
        / (2 * p.γ₂ * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam)),
     p.β - p.α + p.γ₁ * p.α * (p.β - p.α) / (2 * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam))]

/-- The vector `𝒩₂ = (γ₁α − γ₂ρ, γ₂α)ᵀ` of arXiv:2207.00446v3, p.12. -/
noncomputable def N₂ (p : Params) : Fin 2 → ℝ := ![p.γ₁ * p.α - p.γ₂ * p.ρ, p.γ₂ * p.α]

/-- The scalar `𝒩₀ = 1 / (γ₂²(γ₂ρ − γ₁α + λ))` of arXiv:2207.00446v3, p.12. -/
noncomputable def N₀ (p : Params) : ℝ := 1 / (p.γ₂ ^ 2 * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam))

/-- The rank-one matrix `𝒩₂𝒩₀𝒩₂ᵀ` of arXiv:2207.00446v3, p.12. -/
noncomputable def S (p : Params) : Matrix (Fin 2) (Fin 2) ℝ :=
  p.N₀ • Matrix.vecMulVec p.N₂ p.N₂

/-- The matrix `ℳ` of arXiv:2207.00446v3, p.12. -/
noncomputable def M (p : Params) : Matrix (Fin 2) (Fin 2) ℝ :=
  -!![(p.γ₁ ^ 2 * p.α ^ 2 - 4 * p.lam * p.γ₂ * p.ρ)
        / (4 * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam)),
      p.γ₁ * (p.β - p.α) * (p.γ₁ * p.α - 2 * p.lam)
        / (4 * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam));
      p.γ₁ * (p.β - p.α) * (p.γ₁ * p.α - 2 * p.lam)
        / (4 * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam)),
      p.γ₁ ^ 2 * (p.β - p.α) ^ 2 / (4 * (p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam))]

/-- The terminal matrix of (3.1), `diag(γ₂/2, 0)`, **corrected**: the display on p.12 of
arXiv:2207.00446v3 prints the upper left entry as `γ₂`, but (2.15) has `B₁₁,T = γ₂/2`, and the
terminal value on p.15 is `G + Λ̃` with upper left entry `γ₂/2 + Λα²`. Not to be confused with the
vector `𝒢` of (2.19), which is `Params.G`. -/
noncomputable def termMat (p : Params) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.γ₂ / 2, 0; 0, 0]

/-- The matrix `Λ̃` of arXiv:2207.00446v3, p.12. -/
noncomputable def lamTilde (p : Params) (Λ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Λ * p.α ^ 2, Λ * p.α * (p.β - p.α);
     Λ * p.α * (p.β - p.α), Λ * (p.β - p.α) ^ 2]

/-- The matrix `𝒩̃₁ = 𝒩₁ − Λ̃𝒩₂𝒩₀𝒩₂ᵀ` of arXiv:2207.00446v3, p.12. -/
noncomputable def N₁Tilde (p : Params) (Λ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  p.N₁ - p.lamTilde Λ * p.S

/-- The matrix `ℳ̃ = −Λ̃𝒩₂𝒩₀𝒩₂ᵀΛ̃ + 𝒩₁Λ̃ + Λ̃𝒩₁ᵀ + ℳ` of arXiv:2207.00446v3, p.12. -/
noncomputable def MTilde (p : Params) (Λ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  -(p.lamTilde Λ * p.S * p.lamTilde Λ) + p.N₁ * p.lamTilde Λ + p.lamTilde Λ * p.N₁ᵀ + p.M

end Params

/-- `P` solves the matrix Riccati equation `Ṗ = PSP + NP + PNᵀ − Q` on `[0, T]` with `P_T = G`, the
common form of (3.1) and (3.2), arXiv:2207.00446v3, p.12. The derivative is entrywise, in the sense
of `Params.SolvesA`. -/
def IsMatRiccati {n : ℕ} (S N Q G : Matrix (Fin n) (Fin n) ℝ) (T : ℝ)
    (P : ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ s ∈ Icc 0 T, ∀ i j,
    HasDerivWithinAt (fun u => P u i j) ((P s * S * P s + N * P s + P s * Nᵀ - Q) i j)
      (Icc 0 T) s) ∧
  P T = G

end MFCLiquidation


