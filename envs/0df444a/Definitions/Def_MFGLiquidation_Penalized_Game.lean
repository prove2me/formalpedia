-- Prove2me | Definitions.Def_MFGLiquidation_Penalized_Game
-- name    : MFGLiquidation_Penalized_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:25.751464+00:00
-- url     : https://prove2.me/theorems/6ac17105-96eb-46bb-8e93-6441274f7eeb
-- title:
--   The constrained liquidation problem (𝒜_𝔽(𝒳), J, V, the MFG (1.7)) and the penalized problem (4.1) (Jⁿ, Vⁿ)
-- statement:
--   Given an $\mathbb F^0$-progressive process $\mu$ (the aggregate trading rate), a trading rate $\xi$ produces the portfolio $X^\xi_t=\mathcal X-\int_0^t\xi_s\,ds$.
--
--   **Constrained problem (p. 7).** The admissible controls are
--   $$\mathcal A_{\mathbb F}(\mathcal X)=\Big\{\xi\in L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R):\ \int_0^T\xi_s\,ds=\mathcal X\ \text{a.s.}\Big\},$$
--   the cost is $J(\mathcal X,\xi;\mu)=\mathbb E\big[\int_0^T(\kappa_sX^\xi_s\mu_s+\eta_s\xi_s^2+\lambda_s(X^\xi_s)^2)\,ds\,\big|\,\mathcal X\big]$, and the value is $V(\mathcal X;\mu)=\inf_{\xi\in\mathcal A_{\mathbb F}(\mathcal X)}J(\mathcal X,\xi;\mu)$. A process $\mu\in L^2_{\mathbb F^0}$ solves the MFG (1.7) if some optimal $\xi^*$ satisfies $\mu_t=\mathbb E[\xi^*_t|\mathcal F^0_t]$ for a.e. $t$.
--
--   **Penalized problem (4.1), $n\ge1$.** The liquidation constraint is dropped and open positions at $T$ are penalized:
--   $$J^n(\xi;\mu)=\mathbb E\Big[\int_0^T\big(\kappa_t\mu_tX^\xi_t+\eta_t\xi_t^2+\lambda_t(X^\xi_t)^2\big)dt+n\,(X^\xi_T)^2\,\Big|\,\mathcal X\Big],$$
--   minimized over all $\xi\in L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R)$, with value $V^n(\mathcal X;\mu)=\inf_\xi J^n(\xi;\mu)$.
--
--   These are the two optimization problems whose values Theorem 4.6 compares.
--
--   **Formalization Note.** Both values are conditional essential infima: $V$ is the largest $\sigma(\mathcal X)$-measurable random variable with $V\le J(\mathcal X,\xi;\mu)$ a.s. for every admissible $\xi$ (`IsValue`, `IsValuePen`); no pointwise infimum over controls is taken. The costs are conditional expectations given $\sigma(\mathcal X)$. Under Assumption 2.3, with $\xi,\mu\in L^2$, the integrands are integrable, so the conditional expectations are genuine (no junk value). The penalized control space is not printed in (4.1); it is read as $L^2_{\mathbb F}$, the space of §2, which the proof of Theorem 4.6 uses ("the optimal strategy $\xi^*$ for the constraint optimization is an admissible control for the penalized optimization").
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 5, (1.7); p. 7, 𝒜_𝔽(𝒳), J, V; p. 24, (4.1)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MFGLiquidation_Penalized_Setting

namespace MFGLiquidation.Penalized

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}

/-- The state `X^ξ_t = 𝒳 − ∫_0^t ξ_s ds` driven by a trading rate `ξ`. -/
noncomputable def stateOf (D : Data Ω k) (ξ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  D.𝒳 ω - ∫ s in Set.Icc (0 : ℝ) t, ξ s.toNNReal ω

/-- `𝒜_𝔽(𝒳)` (p. 7): `ξ ∈ L²_𝔽` with `∫_0^T ξ_s ds = 𝒳` a.s. -/
def IsAdmissible {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (ξ : ℝ≥0 → Ω → ℝ) : Prop :=
  L2F (filtF hD) P D.T ξ ∧ ∀ᵐ ω ∂P, ∫ s in Set.Icc (0 : ℝ) D.T, ξ s.toNNReal ω = D.𝒳 ω

/-- `J(𝒳, ξ; μ) = E[∫_0^T (κ_s X_s μ_s + η_s ξ_s² + λ_s X_s²) ds | 𝒳]` (p. 7). -/
noncomputable def cost {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (μ ξ : ℝ≥0 → Ω → ℝ) : Ω → ℝ :=
  P[fun ω => ∫ s in Set.Icc (0 : ℝ) D.T,
      (D.κ s.toNNReal ω * stateOf D ξ s.toNNReal ω * μ s.toNNReal ω
        + D.η s.toNNReal ω * ξ s.toNNReal ω ^ 2
        + D.lam s.toNNReal ω * stateOf D ξ s.toNNReal ω ^ 2)
    | MeasurableSpace.comap D.𝒳 inferInstance]

/-- `ξ` is optimal for the constrained problem given `μ`. -/
def IsOptimal {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (μ ξ : ℝ≥0 → Ω → ℝ) : Prop :=
  IsAdmissible hD ξ ∧ ∀ ξ', IsAdmissible hD ξ' → cost hD μ ξ ≤ᵐ[P] cost hD μ ξ'

/-- `V(𝒳; μ) = inf_{ξ ∈ 𝒜_𝔽(𝒳)} J(𝒳, ξ; μ)`, as the conditional essential infimum: the
largest `σ(𝒳)`-measurable `V` with `V ≤ J(𝒳, ξ; μ)` a.s. for every admissible `ξ`. -/
def IsValue {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (μ : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ) : Prop :=
  Measurable[MeasurableSpace.comap D.𝒳 inferInstance] V ∧
    (∀ ξ, IsAdmissible hD ξ → V ≤ᵐ[P] cost hD μ ξ) ∧
    ∀ V' : Ω → ℝ, Measurable[MeasurableSpace.comap D.𝒳 inferInstance] V' →
      (∀ ξ, IsAdmissible hD ξ → V' ≤ᵐ[P] cost hD μ ξ) → V' ≤ᵐ[P] V

/-- `μ` solves the MFG (1.7). -/
def IsMFGSolution {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (μ : ℝ≥0 → Ω → ℝ) : Prop :=
  L2F (filtF0 hD) P D.T μ ∧
    ∃ ξ, IsOptimal hD μ ξ ∧ IsCondExpVersion (filtF0 hD) P D.T ξ μ

/-- Admissible controls of the penalized problem (4.1): `ξ ∈ L²_𝔽`, no terminal constraint. -/
def IsAdmissiblePen {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (ξ : ℝ≥0 → Ω → ℝ) : Prop :=
  L2F (filtF hD) P D.T ξ

/-- `Jⁿ(ξ; μ) = E[∫_0^T (κ_t μ_t X_t + η_t ξ_t² + λ_t X_t²) dt + n X_T² | 𝒳]` (4.1). -/
noncomputable def costPen {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (n : ℕ)
    (μ ξ : ℝ≥0 → Ω → ℝ) : Ω → ℝ :=
  P[fun ω => (∫ s in Set.Icc (0 : ℝ) D.T,
      (D.κ s.toNNReal ω * μ s.toNNReal ω * stateOf D ξ s.toNNReal ω
        + D.η s.toNNReal ω * ξ s.toNNReal ω ^ 2
        + D.lam s.toNNReal ω * stateOf D ξ s.toNNReal ω ^ 2))
      + (n : ℝ) * stateOf D ξ D.T ω ^ 2
    | MeasurableSpace.comap D.𝒳 inferInstance]

/-- `Vⁿ(𝒳; μ) = inf_ξ Jⁿ(ξ; μ)`, the conditional essential infimum over `L²_𝔽` controls. -/
def IsValuePen {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (n : ℕ)
    (μ : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ) : Prop :=
  Measurable[MeasurableSpace.comap D.𝒳 inferInstance] V ∧
    (∀ ξ, IsAdmissiblePen hD ξ → V ≤ᵐ[P] costPen hD n μ ξ) ∧
    ∀ V' : Ω → ℝ, Measurable[MeasurableSpace.comap D.𝒳 inferInstance] V' →
      (∀ ξ, IsAdmissiblePen hD ξ → V' ≤ᵐ[P] costPen hD n μ ξ) → V' ≤ᵐ[P] V

end MFGLiquidation.Penalized


