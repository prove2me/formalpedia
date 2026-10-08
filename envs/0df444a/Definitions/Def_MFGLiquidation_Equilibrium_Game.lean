-- Prove2me | Definitions.Def_MFGLiquidation_Equilibrium_Game
-- name    : MFGLiquidation_Equilibrium_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:37.106165+00:00
-- url     : https://prove2.me/theorems/3f2cc243-a77d-4f8e-a0c2-6c638ac89ce3
-- title:
--   Admissible liquidation strategies 𝒜_𝔽(𝒳), conditional cost J(𝒳, ξ; µ), value V(𝒳; µ) and the MFG (1.7)
-- statement:
--   In the setting of the mission, a trading rate $\xi$ determines the portfolio $X^\xi_t=\mathcal X-\int_0^t\xi_s\,ds$. The **admissible controls** are
--   $$\mathcal A_{\mathbb F}(\mathcal X)=\Big\{\xi\in L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R):\ \int_0^T\xi_s\,ds=\mathcal X\ \text{a.s.}\Big\},$$
--   i.e. the strategies that liquidate the initial portfolio by time $T$. Given an $\mathbb F^0$-progressive process $\mu$ (the aggregate trading rate), the **cost** of $\xi$ is the conditional expectation
--   $$J(\mathcal X,\xi;\mu)=\mathbb E\Big[\int_0^T\big(\kappa_sX^\xi_s\mu_s+\eta_s\xi_s^2+\lambda_s(X^\xi_s)^2\big)ds\ \Big|\ \mathcal X\Big].$$
--   A control is **optimal** given $\mu$ if it is admissible and its cost is a.s. at most the cost of every admissible control. The **value** $V(\mathcal X;\mu)=\inf_{\xi\in\mathcal A_{\mathbb F}(\mathcal X)}J(\mathcal X,\xi;\mu)$ is the essential infimum of these costs: a $\sigma(\mathcal X)$-measurable random variable that is a.s. below every cost and a.s. above every other such lower bound. A process $\mu$ **solves the MFG (1.7)** if $\mu\in L^2_{\mathbb F^0}([0,T])$ and some optimal control $\xi^*$ given $\mu$ satisfies the fixed-point condition $\mu_t=\mathbb E[\xi^*_t\mid\mathcal F^0_t]$ for a.e. $t\in[0,T]$.
--
--   This is the representative player's liquidation problem under a frozen aggregate rate, and the consistency condition that defines a mean-field equilibrium with common noise $W^0$.
--
--   **Formalization Note** The cost is a conditional expectation given $\sigma(\mathcal X)$ and optimality is a.s., as on p. 7; an unconditional expectation would be a weaker notion. The value is an essential infimum (`IsValue`), never a pointwise infimum over controls. Under Assumption 2.3, for $\xi\in L^2_{\mathbb F}$ and $\mu\in L^2$, the integrand of $J$ is integrable, so the conditional expectation takes no junk value; no integrability is added by hand to `cost`. The fixed point uses an $\mathbb F^0$-progressive version of $t\mapsto\mathbb E[\xi^*_t\mid\mathcal F^0_t]$ (`IsCondExpVersion`), and $\mu$ itself is $\mathbb F^0$-progressive, as step 1 of (1.7) requires. The optimal control in the fixed point is existentially quantified; the paper speaks of "the" optimal strategy.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, pp. 4–5, (1.7); p. 7, 𝒜_𝔽(𝒳), J(𝒳, ξ; µ), V(𝒳; µ)

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}

/-- The state process `X^ξ_t = 𝒳 − ∫_0^t ξ_s ds` of a trading rate `ξ` ((1.7)). -/
noncomputable def stateOf (D : Data Ω k) (ξ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  D.𝒳 ω - ∫ s in Set.Icc (0 : ℝ) t, ξ s.toNNReal ω

/-- The admissible controls `𝒜_𝔽(𝒳) := {ξ ∈ L²_𝔽([0, T]), ∫_0^T ξ_s ds = 𝒳 a.s.}` (p. 7). -/
def IsAdmissible {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (ξ : ℝ≥0 → Ω → ℝ) :
    Prop :=
  L2F (filtF hD) P D.T ξ ∧ ∀ᵐ ω ∂P, ∫ s in Set.Icc (0 : ℝ) D.T, ξ s.toNNReal ω = D.𝒳 ω

/-- The conditional cost `J(𝒳, ξ; μ) := E[∫_0^T (κ_s X_s μ_s + η_s ξ_s² + λ_s X_s²) ds | 𝒳]`
(p. 7), with `X = X^ξ`. -/
noncomputable def cost {D : Data Ω k} {P : Measure Ω} (_hD : D.Standing P)
    (μ ξ : ℝ≥0 → Ω → ℝ) : Ω → ℝ :=
  P[fun ω => ∫ s in Set.Icc (0 : ℝ) D.T,
      (D.κ s.toNNReal ω * stateOf D ξ s.toNNReal ω * μ s.toNNReal ω +
        D.η s.toNNReal ω * ξ s.toNNReal ω ^ 2 +
        D.lam s.toNNReal ω * stateOf D ξ s.toNNReal ω ^ 2) |
    MeasurableSpace.comap D.𝒳 inferInstance]

/-- `ξ` is an optimal control for the representative player given `μ`: admissible, and its
conditional cost is a.s. at most that of every admissible control. -/
def IsOptimal {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (μ ξ : ℝ≥0 → Ω → ℝ) :
    Prop :=
  IsAdmissible hD ξ ∧ ∀ ξ', IsAdmissible hD ξ' → cost hD μ ξ ≤ᵐ[P] cost hD μ ξ'

/-- `V` is the value function `V(𝒳; μ) = inf_{ξ ∈ 𝒜_𝔽(𝒳)} J(𝒳, ξ; μ)` (p. 7), read as the
essential infimum of the conditional costs among `σ(𝒳)`-measurable random variables. -/
def IsValue {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (μ : ℝ≥0 → Ω → ℝ)
    (V : Ω → ℝ) : Prop :=
  Measurable[MeasurableSpace.comap D.𝒳 inferInstance] V ∧
    (∀ ξ, IsAdmissible hD ξ → V ≤ᵐ[P] cost hD μ ξ) ∧
    ∀ V' : Ω → ℝ, Measurable[MeasurableSpace.comap D.𝒳 inferInstance] V' →
      (∀ ξ, IsAdmissible hD ξ → V' ≤ᵐ[P] cost hD μ ξ) → V' ≤ᵐ[P] V

/-- `μ` solves the MFG (1.7): `μ ∈ L²_{𝔽⁰}([0, T])`, and some optimal control `ξ*` given `μ`
satisfies the fixed-point condition `μ_t = E[ξ*_t | 𝓕⁰_t]` for a.e. `t ∈ [0, T]`. -/
def IsMFGSolution {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (μ : ℝ≥0 → Ω → ℝ) :
    Prop :=
  L2F (filtF0 hD) P D.T μ ∧
    ∃ ξ, IsOptimal hD μ ξ ∧ IsCondExpVersion (filtF0 hD) P D.T ξ μ

end MFGLiquidation.Equilibrium


