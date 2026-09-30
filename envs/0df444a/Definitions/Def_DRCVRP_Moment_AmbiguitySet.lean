-- Prove2me | Definitions.Def_DRCVRP_Moment_AmbiguitySet
-- name    : DRCVRP_Moment_AmbiguitySet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:26:20.418033+00:00
-- url     : https://prove2.me/theorems/0785d89d-5d30-4311-9d39-70c82cf78cb9
-- title:
--   Moment ambiguity set (4), worst-case value-at-risk and the demand estimator $d_{\mathcal P}$ of (2)
-- statement:
--   Consider $n$ customers with uncertain demand vector $\tilde{\boldsymbol q}\in\mathbb R^n$, whose distribution is not known exactly but only known to lie in an **ambiguity set** $\mathcal P$ of probability distributions on $\mathbb R^n$.
--
--   1. **Moment ambiguity set.** Fix a rectangular support $\mathcal Q=[\underline{\boldsymbol q},\overline{\boldsymbol q}]\subseteq\mathbb R^n$, a mean vector $\boldsymbol\mu\in\mathbb R^n$, a **dispersion measure** $\boldsymbol\varphi=(\varphi_1,\dots,\varphi_p):\mathbb R^n\to\mathbb R^p$ and dispersion bounds $\boldsymbol\sigma\in\mathbb R^p$. The moment ambiguity set is
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^n):\ \mathbb P(\tilde{\boldsymbol q}\in\mathcal Q)=1,\ \ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \ \mathbb E_{\mathbb P}[\boldsymbol\varphi(\tilde{\boldsymbol q})]\le\boldsymbol\sigma\Big\},
--   $$
--   where $\mathcal P_0(\mathbb R^n)$ is the set of all probability distributions on $\mathbb R^n$ and the last inequality is componentwise.
--
--   2. **Worst-case value-at-risk.** For a distribution $\mathbb P$ and a real random variable $\tilde X$, $\mathbb P\text{-VaR}_{1-\epsilon}[\tilde X]=\inf\{x\in\mathbb R:\mathbb P[\tilde X\le x]\ge1-\epsilon\}$. For a customer subset $S$ the worst-case value-at-risk of its cumulative demand is
--   $$
--   \sup_{\mathbb P\in\mathcal P}\ \mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big].
--   $$
--
--   3. **Demand estimator.** For a vehicle capacity $Q>0$,
--   $$
--   d_{\mathcal P}(S)=\max\left\{\left\lceil\frac1Q\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big]\right\rceil,\ 1\right\}\quad\forall S\neq\emptyset,\qquad d_{\mathcal P}(\emptyset)=0,
--   $$
--   a lower bound on the number of vehicles needed to serve the customers in $S$.
--
--   4. **Two-point distributions.** For weights $p_1,p_2\ge0$ and points $\boldsymbol q_1,\boldsymbol q_2\in\mathbb R^n$, the measure $p_1\cdot\delta_{\boldsymbol q_1}+p_2\cdot\delta_{\boldsymbol q_2}$.
--
--   The demand estimator enters the rounded capacity inequalities of the two-index vehicle flow formulation 2VF($\mathcal P$) of the distributionally robust capacitated vehicle routing problem; whether it is subadditive decides whether that formulation is exact.
--
--   **Formalization Note** Customers are `Fin n` (0-based). Distributions are measures on `Fin n → ℝ` with its product (= Borel) σ-algebra. The set `momentAmbiguitySet qlo qhi μ φ σ` requires `IsProbabilityMeasure P`, `P (Set.Icc qlo qhi) = 1`, for each customer `i` integrability of the coordinate and `∫ q, q i ∂P = μ i`, and for each `l` integrability of `φ l` and `∫ q, φ l q ∂P ≤ σ l`. The integrability clauses are automatic for a measure carried by the bounded box when each `φ l` is continuous (in particular convex), so they do not change the set under the paper's standing assumptions. The value-at-risk is the published `MultistageStochastic.valueAtRisk P Y (1 - ε)`. The worst-case VaR is a real `sSup` over the image of the ambiguity set; over a moment set satisfying the standing assumptions this image is nonempty (the Dirac measure at $\boldsymbol\mu$ belongs to the set) and bounded (all VaRs lie between $\sum_{i\in S}\underline q_i$ and $\sum_{i\in S}\overline q_i$), so `sSup` is the true supremum. The estimator is integer valued (`ℤ`); `⌈x / Q⌉` is the paper's $\lceil\frac1Q x\rceil$.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 720 (value-at-risk), p. 721, Eq. (2) (demand estimator), p. 722, Eq. (4) (moment ambiguity set), p. 723, Proposition 1 (two-point distributions)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional

open MeasureTheory

namespace DRCVRP.Moment

/-- The moment ambiguity set (4) (Ghosal–Wiesemann, §3, p. 722):
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ(q̃ ∈ 𝒬) = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[φ(q̃)] ≤ σ}` with the rectangular support
`𝒬 = [qlo, qhi]`, the mean vector `μ`, the dispersion measure `φ : ℝⁿ → ℝᵖ` (component `l` is
`φ l`) and the dispersion bounds `σ`. Customers are `Fin n` (0-based). The integrability clauses
make the expectations genuine Bochner integrals; they hold automatically for a probability measure
carried by the box when each `φ l` is continuous (e.g. convex). -/
def momentAmbiguitySet {n p : ℕ} (qlo qhi μ : Fin n → ℝ) (φ : Fin p → (Fin n → ℝ) → ℝ)
    (σ : Fin p → ℝ) : Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ i, Integrable (fun q => q i) P ∧ ∫ q, q i ∂P = μ i) ∧
    ∀ l, Integrable (φ l) P ∧ ∫ q, φ l q ∂P ≤ σ l}

/-- The worst-case value-at-risk `sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]` of the cumulative demand
of the customer subset `S` over an ambiguity set `Amb` (the paper's `𝒫`) (§3, p. 721). -/
noncomputable def worstCaseVaR {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  sSup ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb)

/-- The demand estimator (2) (§3, p. 721):
`d_𝒫(S) = max {⌈(1/Q) sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]⌉, 1}` for `S ≠ ∅`, and
`d_𝒫(∅) = 0`. -/
noncomputable def demandEstimator {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε Q : ℝ)
    (S : Finset (Fin n)) : ℤ :=
  if S = ∅ then 0 else max ⌈worstCaseVaR Amb ε S / Q⌉ 1

/-- The two-point distribution `p₁ · δ_{q₁} + p₂ · δ_{q₂}` on `ℝⁿ` (§3, p. 723, Proposition 1). -/
noncomputable def twoPointMeasure {n : ℕ} (p₁ p₂ : ℝ) (q₁ q₂ : Fin n → ℝ) :
    Measure (Fin n → ℝ) :=
  ENNReal.ofReal p₁ • Measure.dirac q₁ + ENNReal.ofReal p₂ • Measure.dirac q₂

end DRCVRP.Moment


