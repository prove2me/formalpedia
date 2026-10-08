-- Prove2me | Definitions.Def_VarianceRegularization_FastRates_Setting
-- name    : VarianceRegularization_FastRates_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:43:27.013986+00:00
-- url     : https://prove2.me/theorems/16b36aab-314c-46e8-b2eb-a0f7421c7ac1
-- title:
--   §4.1 — risk, robust risk, ε-suboptimal sets, projection onto S⋆, localized Rademacher complexity and Δ_n
-- statement:
--   Let $\Theta\subseteq\mathbb R^d$ (with the Euclidean norm), let $\ell:\mathbb R^d\times\mathcal X\to\mathbb R$ be a loss, $P$ a probability distribution on $\mathcal X$, and $X_1,\dots,X_n$ a sample. This file fixes the objects of §4.1 and Appendix E.
--
--   1. The **risk** $R(\theta)=\mathbb E_P[\ell(\theta;X)]$ (eq. (1)) and the **robust risk** $R_n(\theta,\mathcal P_n)=\sup_{p\in\mathcal P_n}\sum_i p_i\,\ell(\theta;X_i)$ (eq. (4)).
--   2. For $\epsilon\ge0$, the **$\epsilon$-suboptimal sets**
--   $$S_\star^\epsilon=\Big\{\theta\in\Theta: R(\theta)\le\inf_{\theta^\star\in\Theta}R(\theta^\star)+\epsilon\Big\},\qquad \widehat S_\star^\epsilon=\Big\{\theta\in\Theta: R_n(\theta,\mathcal P_n)\le\inf_{\theta'\in\Theta}R_n(\theta',\mathcal P_n)+\epsilon\Big\},$$
--   and $S_\star=S_\star^0$.
--   3. The **Euclidean projection** $\pi_{S_\star}(\theta)=\mathrm{argmin}_{\theta^\star\in S_\star}\|\theta^\star-\theta\|_2$.
--   4. For $A\subseteq\Theta$, the **localized class** $\{x\mapsto\ell(\theta;x)-\ell(\pi_{S_\star}(\theta);x):\theta\in A\}$ and its empirical Rademacher complexity
--   $$\mathfrak R_n(A)=\mathbb E_\varepsilon\Big[\sup_{\theta\in A}\frac1n\sum_{i=1}^n\varepsilon_i\big(\ell(\theta;X_i)-\ell(\pi_{S_\star}(\theta);X_i)\big)\Big],$$
--   the $\varepsilon_i$ i.i.d. uniform on $\{-1,1\}$.
--   5. The **localized empirical deviation** (41)
--   $$\Delta_n(\theta)=\mathbb E\big[\ell(\theta;X)-\ell(\pi(\theta);X)\big]-\mathbb E_{\widehat P_n}\big[\ell(\theta;X)-\ell(\pi(\theta);X)\big].$$
--
--   These are the quantities in which Theorem 5 and its proof are stated.
--
--   **Formalization Note** The suboptimal sets are written without an infimum: $\theta\in\Theta$ with $R(\theta)\le R(\theta')+\epsilon$ for every $\theta'\in\Theta$; this agrees with the paper's sets whenever the infimum is finite, and gives the empty set when it is $-\infty$. The projection picks a nearest point of $S_\star$ when one exists (for $S_\star$ nonempty, closed and convex it exists and is unique); the theorems assume $S_\star$ nonempty and closed, so the fallback value is never used. The Rademacher complexity is the published `UnderstandingML.rademacher` of the evaluation set of the localized class at the sample (average over the $2^n$ sign vectors).
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 2, eqs. (1), (4); p. 7, §2.2 (Rademacher complexity); p. 19, §4.1; p. 44, eq. (41)

import Mathlib
import Definitions.Def_VarianceRegularization_FastRates_RobustRisk
import Definitions.Def_UnderstandingML_Rademacher

open MeasureTheory

namespace VarianceRegularization.FastRates

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-- The population risk `R(θ) = 𝔼_P[ℓ(θ; X)]` (eq. (1)). -/
noncomputable def risk (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (P : Measure X)
    (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ x, ℓ θ x ∂P

/-- The robustly regularized empirical risk `R_n(θ, 𝒫_n) = sup_{p ∈ 𝒫_n} ∑ᵢ pᵢ ℓ(θ; Xᵢ)`
(eq. (4)) at the sample `s = (X₁, …, X_n)`. -/
noncomputable def robustRisk {n : ℕ} (ρ : ℝ) (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ)
    (s : Fin n → X) (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  VarianceRegularization.Expansion.robustSup n ρ (fun i => ℓ θ (s i))

/-- The `ε`-suboptimal set `S_⋆^ε = {θ ∈ Θ : R(θ) ≤ inf_{θ⋆ ∈ Θ} R(θ⋆) + ε}` (p. 19), written
without an infimum: `R(θ) ≤ R(θ') + ε` for every `θ' ∈ Θ`. `S_⋆ := S_⋆^0`. -/
def subOptSet (Θ : Set (EuclideanSpace ℝ (Fin d))) (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ)
    (P : Measure X) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {θ | θ ∈ Θ ∧ ∀ θ' ∈ Θ, risk ℓ P θ ≤ risk ℓ P θ' + ε}

/-- The empirical `ε`-suboptimal set
`Ŝ_⋆^ε = {θ ∈ Θ : R_n(θ, 𝒫_n) ≤ inf_{θ' ∈ Θ} R_n(θ', 𝒫_n) + ε}` (p. 19), written without an
infimum. -/
def empSubOptSet (Θ : Set (EuclideanSpace ℝ (Fin d))) {n : ℕ} (ρ : ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (s : Fin n → X) (ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {θ | θ ∈ Θ ∧ ∀ θ' ∈ Θ, robustRisk ρ ℓ s θ ≤ robustRisk ρ ℓ s θ' + ε}

/-- The Euclidean projection `π_K(θ) = argmin_{y ∈ K} ‖y − θ‖₂` (p. 19): a nearest point of `K`
to `θ` when one exists (for `K` nonempty, closed and convex it exists and is unique); the
fallback value `θ` is never used under those hypotheses. -/
noncomputable def proj (K : Set (EuclideanSpace ℝ (Fin d))) (θ : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  open Classical in
  if h : ∃ y ∈ K, ∀ z ∈ K, ‖θ - y‖ ≤ ‖θ - z‖ then h.choose else θ

/-- The localized loss class `{x ↦ ℓ(θ; x) − ℓ(π_{S_⋆}(θ); x) : θ ∈ A}` (p. 19). -/
def localizedClass (Θ : Set (EuclideanSpace ℝ (Fin d))) (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ)
    (P : Measure X) (A : Set (EuclideanSpace ℝ (Fin d))) : Set (X → ℝ) :=
  {g | ∃ θ ∈ A, g = fun x => ℓ θ x - ℓ (proj (subOptSet Θ ℓ P 0) θ) x}

/-- The empirical Rademacher complexity `𝔑_n(A)` of the localized process at the sample `s`
(pp. 7, 19): `𝔼_σ[sup_{θ ∈ A} (1/n) ∑ᵢ σᵢ (ℓ(θ; Xᵢ) − ℓ(π_{S_⋆}(θ); Xᵢ))]`, the expectation over
i.i.d. uniform signs `σᵢ ∈ {±1}`; this is `R(F ∘ S)` of Shalev-Shwartz–Ben-David (26.4)–(26.5). -/
noncomputable def localizedRademacher (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (P : Measure X) (A : Set (EuclideanSpace ℝ (Fin d)))
    {n : ℕ} (s : Fin n → X) : ℝ :=
  UnderstandingML.rademacher (UnderstandingML.evalSet (localizedClass Θ ℓ P A) s)

/-- The localized empirical deviation (41):
`Δ_n(θ) = 𝔼[ℓ(θ; X) − ℓ(π(θ); X)] − 𝔼_{P̂_n}[ℓ(θ; X) − ℓ(π(θ); X)]`, `π = π_{S_⋆}`. -/
noncomputable def localizedDeviation (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (P : Measure X) {n : ℕ} (s : Fin n → X)
    (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (∫ x, (ℓ θ x - ℓ (proj (subOptSet Θ ℓ P 0) θ) x) ∂P)
    - VarianceRegularization.Expansion.empMean (fun i => ℓ θ (s i) - ℓ (proj (subOptSet Θ ℓ P 0) θ) (s i))

end VarianceRegularization.FastRates


