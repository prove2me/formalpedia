-- Prove2me | Definitions.Def_DRCVRP_Marginal_AmbiguitySets
-- name    : DRCVRP_Marginal_AmbiguitySets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:37:33.240695+00:00
-- url     : https://prove2.me/theorems/ca59d310-9729-439d-8a1c-e34d2fef64d7
-- title:
--   Marginalized moment, first-order, variance and semivariance ambiguity sets (5), (6), (8), (10)
-- statement:
--   Let $\tilde{\boldsymbol q}\in\mathbb R^n$ be the random demand vector of $n$ customers, with support box $\mathcal Q=[\underline{\boldsymbol q},\overline{\boldsymbol q}]$, mean vector $\boldsymbol\mu\in\mathbb R^n$, and let $\mathcal P_0(\mathbb R^n)$ be the set of all probability distributions on $\mathbb R^n$. Write $[x]_+=\max\{x,0\}$. The following **marginalized** ambiguity sets constrain each customer's demand separately; they contain joint distributions of arbitrary dependence structure.
--
--   1. **Marginalized moment ambiguity set (5).** For each customer $i$, a dispersion measure $\boldsymbol\varphi_i:\mathbb R\to\mathbb R^{p_i}$ and a bound $\boldsymbol\sigma_i\in\mathbb R^{p_i}$:
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^n):\ \mathbb P(\tilde{\boldsymbol q}\in\mathcal Q)=1,\ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \mathbb E_{\mathbb P}[\boldsymbol\varphi_i(\tilde q_i)]\le\boldsymbol\sigma_i\ \ \forall i\in V_C\Big\},
--   $$
--   the last inequality componentwise.
--
--   2. **Marginalized first-order ambiguity set (6).** For $\boldsymbol\sigma\in\mathbb R^n$:
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^n):\ \mathbb P(\tilde{\boldsymbol q}\in\mathcal Q)=1,\ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \mathbb E_{\mathbb P}\big[|\tilde{\boldsymbol q}-\boldsymbol\mu|\big]\le\boldsymbol\sigma\Big\},
--   $$
--   with $|\cdot|$ and $\le$ componentwise: $\sigma_i$ bounds the mean absolute deviation of $\tilde q_i$.
--
--   3. **Marginalized variance ambiguity set (8).**
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^n):\ \mathbb P[\tilde{\boldsymbol q}\in\mathcal Q]=1,\ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \mathbb E_{\mathbb P}\big[(\tilde q_i-\mu_i)^2\big]\le\sigma_i\ \ \forall i\in V_C\Big\}:
--   $$
--   $\sigma_i$ bounds the variance (not the standard deviation) of $\tilde q_i$.
--
--   4. **Marginalized semivariance ambiguity set (10).** For $\boldsymbol\sigma^+,\boldsymbol\sigma^-\in\mathbb R^n$:
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^n):\ \mathbb P[\tilde{\boldsymbol q}\in\mathcal Q]=1,\ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \mathbb E_{\mathbb P}\big[[\tilde q_i-\mu_i]_+^2\big]\le\sigma_i^+,\ \mathbb E_{\mathbb P}\big[[\mu_i-\tilde q_i]_+^2\big]\le\sigma_i^-\ \ \forall i\in V_C\Big\}.
--   $$
--
--   The sets (6), (8) and (10) are the special cases $\varphi_i(q_i)=|q_i-\mu_i|$, $\varphi_i(q_i)=(q_i-\mu_i)^2$ and $\boldsymbol\varphi_i(q_i)=([q_i-\mu_i]_+^2,[\mu_i-q_i]_+^2)$ of (5). The paper's standing assumptions ($\underline{\boldsymbol q}\ge\mathbf 0$, $\boldsymbol\mu\in\operatorname{int}\mathcal Q$, convexity of $\boldsymbol\varphi_i$ with $\boldsymbol\varphi_i(\mu_i)<\boldsymbol\sigma_i$, and $\boldsymbol\sigma,\boldsymbol\sigma^\pm>\mathbf 0$) are not part of the sets; they are hypotheses of the theorems that use them.
--
--   **Formalization Note** Distributions are measures on `Fin n → ℝ` with its product (Borel) σ-algebra; membership requires `IsProbabilityMeasure P`. The support condition is `P (Set.Icc qlo qhi) = 1`, the mean condition `∀ i, ∫ q, q i ∂P = μ i`. In (5), $\boldsymbol\varphi_i$ has components `φ i l : ℝ → ℝ`, `l : Fin (p i)`, and each expectation is required to exist (`Integrable`) and to be at most `σ i l`; for the continuous integrands of (6), (8), (10), and for convex $\varphi_{i,l}$, integrability is automatic on the bounded support, so it is not written there.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §4, p. 723, Eq. (5); §4.1, p. 724, Eq. (6); §4.2, pp. 724–725, Eq. (8); §4.3, p. 725, Eq. (10)

import Mathlib

open MeasureTheory

namespace DRCVRP.Marginal

/-!
The marginalized moment ambiguity sets of Ghosal and Wiesemann, *The Distributionally Robust
Chance-Constrained Vehicle Routing Problem*, Oper. Res. 68(3) (2020), §4, pp. 723–725. Each is a
set of probability measures on `ℝⁿ = Fin n → ℝ` (joint laws of the demand vector, not products of
marginals). The support `𝒬 = [q̲, q̄]` is the box `Set.Icc qlo qhi`. The standing assumptions
(`q̲ ≥ 0`, `μ ∈ int 𝒬`, convexity, positivity of the bounds) are hypotheses of the theorems.
-/

/-- The marginalized moment ambiguity set (5) (§4, p. 723):
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ(q̃ ∈ 𝒬) = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[φ_i(q̃_i)] ≤ σ_i ∀ i ∈ V_C}`, where
`φ_i : ℝ → ℝ^{p_i}` has components `φ i l` and `σ_i ∈ ℝ^{p_i}` has components `σ i l`; the vector
inequality is componentwise. The expectation `𝔼_ℙ[φ_i(q̃_i)]` is required to exist
(integrability); for the closed convex `φ_i` of the paper this is automatic on the bounded
support. -/
def marginalSet {n : ℕ} (qlo qhi μ : Fin n → ℝ) {p : Fin n → ℕ}
    (φ : (i : Fin n) → Fin (p i) → ℝ → ℝ) (σ : (i : Fin n) → Fin (p i) → ℝ) :
    Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ i, ∫ q, q i ∂P = μ i) ∧
    ∀ i l, Integrable (fun q : Fin n → ℝ => φ i l (q i)) P ∧ ∫ q, φ i l (q i) ∂P ≤ σ i l}

/-- The marginalized first-order ambiguity set (6) (§4.1, p. 724):
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ(q̃ ∈ 𝒬) = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[|q̃ - μ|] ≤ σ}`, the absolute value and the
inequality taken componentwise: `σ_i` bounds the mean absolute deviation of `q̃_i`. -/
def firstOrderSet {n : ℕ} (qlo qhi μ σ : Fin n → ℝ) : Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ i, ∫ q, q i ∂P = μ i) ∧ ∀ i, ∫ q, |q i - μ i| ∂P ≤ σ i}

/-- The marginalized variance ambiguity set (8) (§4.2, pp. 724–725):
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ[q̃ ∈ 𝒬] = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[(q̃_i - μ_i)²] ≤ σ_i ∀ i ∈ V_C}`:
`σ_i` bounds the variance of `q̃_i`. -/
def varianceSet {n : ℕ} (qlo qhi μ σ : Fin n → ℝ) : Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ i, ∫ q, q i ∂P = μ i) ∧ ∀ i, ∫ q, (q i - μ i) ^ 2 ∂P ≤ σ i}

/-- The marginalized semivariance ambiguity set (10) (§4.3, p. 725):
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ[q̃ ∈ 𝒬] = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[[q̃_i - μ_i]₊²] ≤ σ_i⁺,
𝔼_ℙ[[μ_i - q̃_i]₊²] ≤ σ_i⁻ ∀ i ∈ V_C}` with `[x]₊ = max x 0`: `σ⁺` and `σ⁻` bound the upper and
the lower semivariance. -/
def semivarianceSet {n : ℕ} (qlo qhi μ σplus σminus : Fin n → ℝ) :
    Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ i, ∫ q, q i ∂P = μ i) ∧
    (∀ i, ∫ q, (max (q i - μ i) 0) ^ 2 ∂P ≤ σplus i) ∧
    ∀ i, ∫ q, (max (μ i - q i) 0) ^ 2 ∂P ≤ σminus i}

end DRCVRP.Marginal


