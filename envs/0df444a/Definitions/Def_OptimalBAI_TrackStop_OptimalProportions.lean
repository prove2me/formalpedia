-- Prove2me | Definitions.Def_OptimalBAI_TrackStop_OptimalProportions
-- name    : OptimalBAI_TrackStop_OptimalProportions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:09:55.83544+00:00
-- url     : https://prove2.me/theorems/52ef3372-22c3-41b3-a8cc-cc28f83996e8
-- title:
--   Optimal proportions $w^*(\boldsymbol\mu)$ of arm draws (eq. (1))
-- statement:
--   Fix a canonical exponential family with divergence $d$ on its mean space $\dot b(\Theta)$. In the mean parameterization, the class $\mathcal S$ is the set of vectors $\boldsymbol\lambda=(\lambda_1,\dots,\lambda_K)$ with every $\lambda_a\in\dot b(\Theta)$ and an arm $a^*(\boldsymbol\lambda)$ with $\lambda_{a^*(\boldsymbol\lambda)}>\lambda_i$ for all $i\ne a^*(\boldsymbol\lambda)$. For a mean vector $\boldsymbol\mu$,
--   $$\mathrm{Alt}(\boldsymbol\mu)=\{\boldsymbol\lambda\in\mathcal S:\ a^*(\boldsymbol\lambda)\ne a^*(\boldsymbol\mu)\},\qquad \Sigma_K=\Big\{w\in\mathbb R^K_+:\ \textstyle\sum_{a=1}^K w_a=1\Big\}.$$
--   The **transportation cost** of proportions $w$ is $\inf_{\boldsymbol\lambda\in\mathrm{Alt}(\boldsymbol\mu)}\sum_{a=1}^K w_a\,d(\mu_a,\lambda_a)$, and $w$ is an **optimal proportion vector** for $\boldsymbol\mu$ when $w\in\Sigma_K$ maximizes it:
--   $$w\in w^*(\boldsymbol\mu)=\operatorname*{argmax}_{w\in\Sigma_K}\ \inf_{\boldsymbol\lambda\in\mathrm{Alt}(\boldsymbol\mu)}\ \sum_{a=1}^K w_a\,d(\mu_a,\lambda_a).$$
--
--   These are the proportions of arm draws that an optimal strategy must realize; both tracking sampling rules of the mission aim at them.
--
--   **Formalization Note** The infimum is computed in the extended reals, so an empty alternative set gives $+\infty$ rather than a default value. Optimality is a predicate on $w$ (no particular maximizer is chosen).
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, pp. 3–4, §2.1, definitions of Alt, Σ_K and eq. (1)

import Mathlib
import Definitions.Def_OptimalBAI_TrackStop_ExpFamily

namespace OptimalBAI.TrackStop

variable {K : ℕ}

/-- Arm `a` is the unique optimal arm of the mean vector `μ`: `μ_a > μ_i` for every `i ≠ a`. -/
def IsBest (μ : Fin K → ℝ) (a : Fin K) : Prop :=
  ∀ i, i ≠ a → μ i < μ a

/-- The class `𝒮` of exponential-family bandit models with a unique optimal arm (paper, p. 4),
in the mean parameterization: mean vectors `λ = (λ_1, …, λ_K)` with every `λ_a` in the mean space
`ḃ(Θ)` and some arm strictly better than all others. -/
def bestArmMeans (F : ExpFamily) (K : ℕ) : Set (Fin K → ℝ) :=
  {lam | (∀ a, lam a ∈ F.M) ∧ ∃ a, IsBest lam a}

/-- `Alt(μ) = {λ ∈ 𝒮 : a*(λ) ≠ a*(μ)}` (paper, p. 3): the models of `𝒮` whose optimal arm is not an
optimal arm of `μ`. -/
def Alt (F : ExpFamily) (μ : Fin K → ℝ) : Set (Fin K → ℝ) :=
  {lam | lam ∈ bestArmMeans F K ∧ ∀ a, IsBest lam a → ¬ IsBest μ a}

/-- The probability simplex `Σ_K = {w ∈ ℝ^K_+ : w_1 + ⋯ + w_K = 1}` (paper, p. 3). -/
def simplex (K : ℕ) : Set (Fin K → ℝ) :=
  {w | (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1}

/-- The transportation cost `inf_{λ ∈ Alt(μ)} ∑_a w_a d(μ_a, λ_a)` of the proportions `w`
(the inner infimum of eq. (1), p. 4). It is computed in `EReal`, so the infimum is the true
infimum of the set of values (an empty `Alt(μ)` would give `⊤`, never a junk `0`). -/
noncomputable def transportCost (F : ExpFamily) (μ w : Fin K → ℝ) : EReal :=
  ⨅ lam ∈ Alt F μ, ((∑ a, w a * F.d (μ a) (lam a) : ℝ) : EReal)

/-- `w` is an optimal proportion vector, i.e. an element of
`w*(μ) = argmax_{w ∈ Σ_K} inf_{λ ∈ Alt(μ)} ∑_a w_a d(μ_a, λ_a)` (paper, p. 4). -/
def IsOptimalProportion (F : ExpFamily) (μ w : Fin K → ℝ) : Prop :=
  w ∈ simplex K ∧ ∀ w' ∈ simplex K, transportCost F μ w' ≤ transportCost F μ w

end OptimalBAI.TrackStop


