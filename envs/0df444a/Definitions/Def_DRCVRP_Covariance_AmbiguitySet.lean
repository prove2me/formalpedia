-- Prove2me | Definitions.Def_DRCVRP_Covariance_AmbiguitySet
-- name    : DRCVRP_Covariance_AmbiguitySet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:23:52.628843+00:00
-- url     : https://prove2.me/theorems/9f67a246-1c14-45bd-a4b0-5033c1a7d4a3
-- title:
--   Covariance ambiguity set (16), worst-case value-at-risk and the bounds $q^\ell$, $q^u$ of (17)
-- statement:
--   Consider $n$ customers with an uncertain demand vector $\tilde{\boldsymbol q}\in\mathbb R^n$ whose distribution is only known to belong to an **ambiguity set** $\mathcal P$ of probability distributions on $\mathbb R^n$.
--
--   1. **Covariance ambiguity set.** Fix a box $\mathcal Q=[\underline{\boldsymbol q},\overline{\boldsymbol q}]\subseteq\mathbb R^n$, a mean vector $\boldsymbol\mu\in\mathbb R^n$ and a symmetric matrix $\Sigma\in\mathbb R^{n\times n}$ (the covariance bound). The covariance ambiguity set is
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^n):\ \mathbb P[\tilde{\boldsymbol q}\in\mathcal Q]=1,\ \ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \ \mathbb E_{\mathbb P}\big[(\tilde{\boldsymbol q}-\boldsymbol\mu)(\tilde{\boldsymbol q}-\boldsymbol\mu)^\top\big]\preceq\Sigma\Big\},
--   $$
--   where $\mathcal P_0(\mathbb R^n)$ is the set of all probability distributions on $\mathbb R^n$ and $A\preceq\Sigma$ means that $\Sigma-A$ is positive semidefinite. The paper assumes $\underline{\boldsymbol q}\ge\mathbf 0$, $\boldsymbol\mu\in\operatorname{int}\mathcal Q$ and $\Sigma\succ0$; these side conditions are hypotheses of every theorem that uses the set.
--
--   2. **Worst-case value-at-risk.** For a distribution $\mathbb P$ and a real random variable $\tilde X$, $\mathbb P\text{-VaR}_{1-\epsilon}[\tilde X]=\inf\{x\in\mathbb R:\mathbb P[\tilde X\le x]\ge1-\epsilon\}$. For a customer subset $S$ the worst-case value-at-risk of its total demand is
--   $$
--   \sup_{\mathbb P\in\mathcal P}\ \mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big].
--   $$
--
--   3. **Bounds.** For $\epsilon\in(0,1)$, componentwise,
--   $$
--   \boldsymbol q^\ell=\max\Big\{-\tfrac{1-\epsilon}{\epsilon}(\overline{\boldsymbol q}-\boldsymbol\mu),\ \underline{\boldsymbol q}-\boldsymbol\mu\Big\},\qquad \boldsymbol q^u=\min\Big\{\tfrac{1-\epsilon}{\epsilon}(\boldsymbol\mu-\underline{\boldsymbol q}),\ \overline{\boldsymbol q}-\boldsymbol\mu\Big\}.
--   $$
--
--   These objects make up the quadratically constrained program (17) that computes the worst-case value-at-risk over the covariance ambiguity set, which in turn is the right-hand side of the rounded capacity inequalities in the distributionally robust vehicle routing problem.
--
--   **Formalization Note** Customers are `Fin n` (0-based). Distributions are measures on `Fin n → ℝ` with its product (= Borel) σ-algebra. `covarianceSet qlo qhi μ Sig` requires `IsProbabilityMeasure P`, `P (Set.Icc qlo qhi) = 1`, `∫ q, q j ∂P = μ j` for every `j`, and `Sig - M` positive semidefinite, where `M` is the matrix of Bochner integrals `∫ (q_i - μ_i)(q_j - μ_j) dP`. No integrability clauses are needed: every integrand is continuous and bounded on the box, which carries all the mass. The value-at-risk is the published `MultistageStochastic.valueAtRisk P Y (1 - ε)`; the worst-case VaR is a real `sSup` over the image of the set, which under the paper's side conditions is nonempty (the Dirac measure at $\boldsymbol\mu$ belongs to the set) and bounded (every VaR lies between $\sum_{i\in S}\underline q_i$ and $\sum_{i\in S}\overline q_i$), so `sSup` is the true supremum. `Sig` stands for $\Sigma$.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 720 (value-at-risk); §5.2, p. 727, Eq. (16) (covariance ambiguity set) and Theorem 7 (bounds q^ℓ, q^u)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional

open MeasureTheory

namespace DRCVRP.Covariance

/-!
The covariance ambiguity set and the worst-case value-at-risk of Ghosal and Wiesemann,
*The Distributionally Robust Chance-Constrained Vehicle Routing Problem*, Oper. Res. 68(3)
(2020), §5.2, p. 727, Eq. (16), and the bounds `q^ℓ`, `q^u` of Theorem 7 (p. 727).

Customers are `Fin n` (the paper's `V_C = {1, …, n}`, 0-based). A demand vector is
`q : Fin n → ℝ`; distributions are measures on `Fin n → ℝ`. The covariance bound `Σ` is
written `Sig`.
-/

/-- The second-moment matrix of `P` centred at `μ`, `𝔼_ℙ[(q̃ - μ)(q̃ - μ)ᵀ]`, entry `(i, j)`
equal to `∫ (q_i - μ_i)(q_j - μ_j) dℙ`. -/
noncomputable def centredSecondMoment {n : ℕ} (μ : Fin n → ℝ) (P : Measure (Fin n → ℝ)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ q, (q i - μ i) * (q j - μ j) ∂P

/-- The covariance ambiguity set (16), p. 727:
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ[q̃ ∈ 𝒬] = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[(q̃ - μ)(q̃ - μ)ᵀ] ⪯ Σ}` with the box support
`𝒬 = [q̲, q̄]`. The Loewner order `A ⪯ Σ` is `Σ - A` positive semidefinite. The side conditions
of (16) (`q̲ ≥ 0`, `μ ∈ int 𝒬`, `Σ ≻ 0`) are hypotheses of the theorems. -/
def covarianceSet {n : ℕ} (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) :
    Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧ (∀ j, ∫ q, q j ∂P = μ j) ∧
    (Sig - centredSecondMoment μ P).PosSemidef}

/-- The worst-case value-at-risk `sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]` of the total demand of
the customer set `S`, with `ℙ-VaR_{1-ε}[X̃] = inf {x : ℙ[X̃ ≤ x] ≥ 1 - ε}` (p. 720). -/
noncomputable def worstCaseVaR {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  sSup ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb)

/-- The lower bound of (17), p. 727: `q^ℓ = max{-((1-ε)/ε)(q̄ - μ), q̲ - μ}`, componentwise. -/
noncomputable def qLower {n : ℕ} (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (j : Fin n) : ℝ :=
  max (-((1 - ε) / ε * (qhi j - μ j))) (qlo j - μ j)

/-- The upper bound of (17) and (18), p. 727: `q^u = min{((1-ε)/ε)(μ - q̲), q̄ - μ}`,
componentwise. -/
noncomputable def qUpper {n : ℕ} (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (j : Fin n) : ℝ :=
  min ((1 - ε) / ε * (μ j - qlo j)) (qhi j - μ j)

end DRCVRP.Covariance


