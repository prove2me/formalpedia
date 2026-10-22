-- Prove2me | Definitions.Def_RiskFunctionals_Frontier_MeanVariance
-- name    : RiskFunctionals_Frontier_MeanVariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:38.167432+00:00
-- url     : https://prove2.me/theorems/3c7fbfac-663e-4eed-8ced-2145ffcc3659
-- title:
--   Mean vector, covariance matrix, portfolio returns, correlation, and the solution sets of the CAPM problems (4.20) and (4.23)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $\xi=(\xi^{(1)},\dots,\xi^{(M)})$ a random vector of asset returns. The book works with *profit* variables: larger returns are better.
--
--   1. The **vector of expected returns** is $r=\mathbb E\xi$, i.e. $r_m=\mathbb E\,\xi^{(m)}$ (4.18).
--   2. The **covariance matrix** is the $M\times M$ matrix $C=\mathrm{Cov}(\xi)$ with entries $C_{ij}=\mathbb{C}\mathrm{ov}(\xi^{(i)},\xi^{(j)})=\mathbb E[(\xi^{(i)}-\mathbb E\xi^{(i)})(\xi^{(j)}-\mathbb E\xi^{(j)})]$.
--   3. The **return of a portfolio** $x=(x_1,\dots,x_M)$ of risky assets is $Y_x=\sum_{m=1}^M x_m\xi^{(m)}$. With a risk-free asset of constant return $r_0$, the portfolio $x=(x_0,\tilde x)$ has return $Y_x=x_0r_0+\sum_{m=1}^M\tilde x_m\xi^{(m)}$.
--   4. The **correlation** of two random variables is
--   $$\mathbb{C}\mathrm{orr}(Y^{(1)},Y^{(2)})=\frac{\mathbb{C}\mathrm{ov}(Y^{(1)},Y^{(2)})}{\sqrt{\mathbb{V}\mathrm{ar}(Y^{(1)})\,\mathbb{V}\mathrm{ar}(Y^{(2)})}}.$$
--   5. For a symmetric matrix $C$, a vector $r\in\mathbb R^M$ and a required return $\mu$, a **solution of (4.20)** is a vector $x\in\mathbb R^M$ that minimizes $x^\top Cx$ subject to $r^\top x=\mu$ and $\mathbb 1^\top x=1$: it is feasible, and $x^\top Cx\le y^\top Cy$ for every feasible $y$.
--   6. With in addition a risk-free return $r_0$, a **solution of (4.23)** is a pair $(x_0,\tilde x)\in\mathbb R\times\mathbb R^M$ that minimizes $\tfrac12\tilde x^\top C\tilde x$ subject to $r^\top\tilde x+r_0x_0=\mu$ and $\mathbb 1_M^\top\tilde x+x_0=1$.
--
--   These are the objects of §4.2.3 (pp. 189–195): the Markowitz/CAPM model without a risk-free asset (4.20) and with one (4.23).
--
--   **Formalization Note** Assets are indexed by `Fin M` (0-based). Expectations are Lebesgue integrals and covariance and variance are Mathlib's `covariance` and `variance`; every theorem using them assumes each $\xi^{(m)}$ has a finite second moment (`MemLp 2`) on a probability space. The correlation divides by $\sqrt{\mathbb{V}\mathrm{ar}\,\mathbb{V}\mathrm{ar}}$, which Lean evaluates to $0$ (and the quotient to $0$) when a variance is $0$; the book's correlation is undefined there, and the theorem using it assumes a positive variance. "Solution" means a global minimizer on the feasible set; uniqueness is not built in and is stated in the theorems where the book asserts it.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 24 (ℂov, ℂorr); p. 25 (covariance matrix); p. 187, Eq. (4.18); p. 189 (Y_x); p. 191, Eq. (4.20); p. 193, Eq. (4.23)

import Mathlib

namespace RiskFunctionals.Frontier

open MeasureTheory ProbabilityTheory Matrix

/-- The vector of expected returns `r = 𝔼ξ` of a random vector `ξ = (ξ⁽¹⁾, …, ξ⁽ᴹ⁾)`
(Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 187, (4.18)):
`r m = 𝔼 ξ⁽ᵐ⁾`. -/
noncomputable def meanVector {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {M : ℕ}
    (ξ : Fin M → Ω → ℝ) : Fin M → ℝ :=
  fun m => ∫ ω, ξ m ω ∂P

/-- The `M × M` covariance matrix `C = Cov(ξ)` of a random vector `ξ` (p. 25 and p. 187):
`C i j = ℂov(ξ⁽ⁱ⁾, ξ⁽ʲ⁾) = 𝔼[(ξ⁽ⁱ⁾ − 𝔼ξ⁽ⁱ⁾)(ξ⁽ʲ⁾ − 𝔼ξ⁽ʲ⁾)]` (Mathlib's `covariance`). -/
noncomputable def covMatrix {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {M : ℕ}
    (ξ : Fin M → Ω → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => covariance (ξ i) (ξ j) P

/-- The return `Y_x = ∑ₘ xₘ ξ⁽ᵐ⁾` of the portfolio `x = (x₁, …, x_M)` of risky assets (p. 189). -/
def portfolioReturn {Ω : Type*} {M : ℕ} (ξ : Fin M → Ω → ℝ) (x : Fin M → ℝ) : Ω → ℝ :=
  fun ω => ∑ m, x m * ξ m ω

/-- The return `Y_x = x₀ r₀ + ∑ₘ x̃ₘ ξ̃⁽ᵐ⁾` of a portfolio `x = (x₀, x̃)` that holds `x₀` in the
risk-free asset with constant return `r₀` and `x̃` in the risky assets `ξ̃` (pp. 192–193). -/
def riskFreeReturn {Ω : Type*} {M : ℕ} (r₀ : ℝ) (ξ : Fin M → Ω → ℝ) (x₀ : ℝ)
    (x : Fin M → ℝ) : Ω → ℝ :=
  fun ω => x₀ * r₀ + ∑ m, x m * ξ m ω

/-- The correlation `ℂorr(Y⁽¹⁾, Y⁽²⁾) = ℂov(Y⁽¹⁾, Y⁽²⁾) / √(𝕍ar(Y⁽¹⁾) 𝕍ar(Y⁽²⁾))` (p. 24).
It is meaningful only when both variances are positive; Lean's `x / 0 = 0` makes it `0`
otherwise, and every theorem using it assumes positive variances. -/
noncomputable def correlation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y₁ Y₂ : Ω → ℝ) : ℝ :=
  covariance Y₁ Y₂ P / Real.sqrt (variance Y₁ P * variance Y₂ P)

/-- `x` is a solution of the CAPM problem without a risk-free asset (p. 191, (4.20)):
minimize `xᵀCx` subject to `rᵀx = μ` and `𝟙ᵀx = 1`. A solution is a feasible point whose
objective is at most that of every feasible point. -/
def IsSolution420 {M : ℕ} (C : Matrix (Fin M) (Fin M) ℝ) (r : Fin M → ℝ) (μ : ℝ)
    (x : Fin M → ℝ) : Prop :=
  r ⬝ᵥ x = μ ∧ (fun _ => (1 : ℝ)) ⬝ᵥ x = 1 ∧
    ∀ y : Fin M → ℝ, r ⬝ᵥ y = μ → (fun _ => (1 : ℝ)) ⬝ᵥ y = 1 → x ⬝ᵥ C *ᵥ x ≤ y ⬝ᵥ C *ᵥ y

/-- `(x₀, x̃)` is a solution of the CAPM problem with a risk-free asset of return `r₀`
(p. 193, (4.23)): minimize `½ x̃ᵀC̃x̃` subject to `r̃ᵀx̃ + r₀x₀ = μ` and `𝟙_Mᵀx̃ + x₀ = 1`. -/
def IsSolution423 {M : ℕ} (C : Matrix (Fin M) (Fin M) ℝ) (r : Fin M → ℝ) (r₀ μ : ℝ)
    (x₀ : ℝ) (x : Fin M → ℝ) : Prop :=
  r ⬝ᵥ x + r₀ * x₀ = μ ∧ (fun _ => (1 : ℝ)) ⬝ᵥ x + x₀ = 1 ∧
    ∀ (y₀ : ℝ) (y : Fin M → ℝ), r ⬝ᵥ y + r₀ * y₀ = μ → (fun _ => (1 : ℝ)) ⬝ᵥ y + y₀ = 1 →
      (1 / 2 : ℝ) * (x ⬝ᵥ C *ᵥ x) ≤ (1 / 2 : ℝ) * (y ⬝ᵥ C *ᵥ y)

end RiskFunctionals.Frontier


