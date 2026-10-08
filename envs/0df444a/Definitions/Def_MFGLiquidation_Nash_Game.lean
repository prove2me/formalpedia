-- Prove2me | Definitions.Def_MFGLiquidation_Nash_Game
-- name    : MFGLiquidation_Nash_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:27.771008+00:00
-- url     : https://prove2.me/theorems/cb58c95a-06bd-440e-8de6-3a7aea6cec45
-- title:
--   Admissible controls 𝒜_𝔽(𝒳), the conditional cost J(𝒳, ξ; µ), the value V(𝒳; µ) and the MFG (1.7)
-- statement:
--   The control layer of the representative player's liquidation problem (p. 7).
--
--   For a trading rate $\xi$ the portfolio is $X^\xi_t=\mathcal X-\int_0^t\xi_s\,ds$. The **admissible controls** are
--   $$\mathcal A_{\mathbb F}(\mathcal X)=\Big\{\xi\in L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R):\ \int_0^T\xi_s\,ds=\mathcal X\ \text{a.s.}\Big\},$$
--   i.e. the liquidation constraint $X^\xi_T=0$. Given a process $\mu$ (the mean-field trading rate), the **conditional cost** is
--   $$J(\mathcal X,\xi;\mu)=\mathbb E\Big[\int_0^T\big(\kappa_sX^\xi_s\mu_s+\eta_s\xi_s^2+\lambda_s(X^\xi_s)^2\big)\,ds\ \Big|\ \mathcal X\Big].$$
--   A control is **optimal** given $\mu$ if it is admissible and its conditional cost is a.s. below that of every admissible control. The **value** $V(\mathcal X;\mu)=\inf_{\xi\in\mathcal A_{\mathbb F}(\mathcal X)}J(\mathcal X,\xi;\mu)$ is the conditional essential infimum: the largest $\sigma(\mathcal X)$-measurable random variable that is a.s. below every $J(\mathcal X,\xi;\mu)$. Finally $\mu$ **solves the MFG (1.7)** if $\mu\in L^2_{\mathbb F^0}$, some $\xi^*$ is optimal given $\mu$, and $\mu_t=\mathbb E[\xi^*_t\mid\mathcal F^0_t]$ for a.e. $t\in[0,T]$.
--
--   These are the objects in terms of which the paper defines its mean-field equilibrium; the $N$-player game of this mission is built on the same cost structure.
--
--   **Formalization Note.** Conditioning on $\mathcal X$ is conditioning on $\sigma(\mathcal X)$. Under Assumption 2.3, for $\xi,\mu\in L^2$ the integrand of $J$ is integrable, so the conditional expectation is not evaluated at a junk value; no integrability is added to the definition. The value is an essential infimum over controls, never a pointwise infimum. The fixed-point condition uses an $\mathbb F^0$-progressive version of $t\mapsto\mathbb E[\xi^*_t\mid\mathcal F^0_t]$.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, pp. 5 and 7, (1.7), the definitions of 𝒜_𝔽(𝒳), J(𝒳, ξ; µ) and V(𝒳; µ)

import Mathlib
import Definitions.Def_MFGLiquidation_Nash_Setting

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Nash

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}

/-- The state `X^ξ_t = 𝒳 − ∫_0^t ξ_s ds` driven by the trading rate `ξ`. -/
noncomputable def stateOf (D : Data Ω k) (ξ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  D.𝒳 ω - ∫ s in Set.Icc (0 : ℝ) t, ξ s.toNNReal ω

/-- Admissible controls `𝒜_𝔽(𝒳)`: `𝔽`-progressive, in `L²`, and `∫_0^T ξ_s ds = 𝒳` a.s. -/
def IsAdmissible {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (ξ : ℝ≥0 → Ω → ℝ) : Prop :=
  L2F (filtF hD) P D.T ξ ∧ ∀ᵐ ω ∂P, ∫ s in Set.Icc (0 : ℝ) D.T, ξ s.toNNReal ω = D.𝒳 ω

/-- The conditional cost
`J(𝒳, ξ; μ) = E[∫_0^T (κ_s X_s μ_s + η_s ξ_s² + λ_s X_s²) ds | 𝒳]`, with `X = X^ξ`. -/
noncomputable def cost {D : Data Ω k} {P : Measure Ω} (_hD : D.Standing P)
    (μ ξ : ℝ≥0 → Ω → ℝ) : Ω → ℝ :=
  P[fun ω => ∫ s in Set.Icc (0 : ℝ) D.T,
      (D.κ s.toNNReal ω * stateOf D ξ s.toNNReal ω * μ s.toNNReal ω
        + D.η s.toNNReal ω * ξ s.toNNReal ω ^ 2
        + D.lam s.toNNReal ω * stateOf D ξ s.toNNReal ω ^ 2)
    | MeasurableSpace.comap D.𝒳 inferInstance]

/-- `ξ` is optimal for the representative player given `μ`: admissible, and its conditional cost
is a.s. below that of every admissible control. -/
def IsOptimal {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (μ ξ : ℝ≥0 → Ω → ℝ) : Prop :=
  IsAdmissible hD ξ ∧ ∀ ξ', IsAdmissible hD ξ' → cost hD μ ξ ≤ᵐ[P] cost hD μ ξ'

/-- `V` is the value `V(𝒳; μ) = ess inf_{ξ ∈ 𝒜_𝔽(𝒳)} J(𝒳, ξ; μ)`: the largest
`σ(𝒳)`-measurable a.s. lower bound of the conditional costs of admissible controls. -/
def IsValue {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (μ : ℝ≥0 → Ω → ℝ)
    (V : Ω → ℝ) : Prop :=
  Measurable[MeasurableSpace.comap D.𝒳 inferInstance] V ∧
    (∀ ξ, IsAdmissible hD ξ → V ≤ᵐ[P] cost hD μ ξ) ∧
    ∀ V' : Ω → ℝ, Measurable[MeasurableSpace.comap D.𝒳 inferInstance] V' →
      (∀ ξ, IsAdmissible hD ξ → V' ≤ᵐ[P] cost hD μ ξ) → V' ≤ᵐ[P] V

/-- `μ` solves the MFG (1.7): `μ ∈ L²_{𝔽⁰}`, there is an optimal `ξ` given `μ`, and `μ` is an
`𝔽⁰`-progressive version of `t ↦ E[ξ_t | 𝓕⁰_t]`. -/
def IsMFGSolution {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (μ : ℝ≥0 → Ω → ℝ) : Prop :=
  L2F (filtF0 hD) P D.T μ ∧
    ∃ ξ, IsOptimal hD μ ξ ∧ IsCondExpVersion (filtF0 hD) P D.T ξ μ

end MFGLiquidation.Nash


