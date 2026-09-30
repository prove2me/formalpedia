-- Prove2me | Definitions.Def_OptimalBAI_OptProportions_OptimalProportions
-- name    : OptimalBAI_OptProportions_OptimalProportions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:58:35.540014+00:00
-- url     : https://prove2.me/theorems/2411381f-1b3e-48b2-8814-b4127a844289
-- title:
--   Alternatives, simplex, transportation cost, optimal proportions $w^*$, $I_\alpha$, $g_a$, $x_a$ and $F_{\boldsymbol\mu}$
-- statement:
--   Fix an exponential family as above, with mean space $\dot b(\Theta)$ and divergence $d$, and $K$ arms. A bandit model is identified with its mean vector $\boldsymbol\mu=(\mu_1,\dots,\mu_K)$.
--
--   1. Arm $a$ is the **unique optimal arm** of $\boldsymbol\mu$ if $\mu_a>\mu_i$ for every $i\ne a$.
--   2. $\mathcal S$ is the set of mean vectors with every coordinate in $\dot b(\Theta)$ that have a unique optimal arm, and
--   $$\mathrm{Alt}(\boldsymbol\mu)=\{\boldsymbol\lambda\in\mathcal S : a^*(\boldsymbol\lambda)\ne a^*(\boldsymbol\mu)\}.$$
--   3. $\Sigma_K=\{w\in\mathbb R_+^K : w_1+\dots+w_K=1\}$ is the probability simplex.
--   4. The **transportation cost** of proportions $w$ is
--   $$c_{\boldsymbol\mu}(w)=\inf_{\boldsymbol\lambda\in\mathrm{Alt}(\boldsymbol\mu)}\sum_{a=1}^K w_a d(\mu_a,\lambda_a),$$
--   and $w$ is an **optimal proportion vector** if $w\in\Sigma_K$ and $c_{\boldsymbol\mu}(w')\le c_{\boldsymbol\mu}(w)$ for all $w'\in\Sigma_K$, i.e. $w$ belongs to $w^*(\boldsymbol\mu)=\operatorname{argmax}_{w\in\Sigma_K}c_{\boldsymbol\mu}(w)$, the maximizer in the definition of the characteristic time $T^*(\boldsymbol\mu)^{-1}=\sup_{w\in\Sigma_K}c_{\boldsymbol\mu}(w)$.
--   5. For $\alpha\in[0,1]$, the parameterized Jensen–Shannon divergence is
--   $$I_\alpha(\mu_1,\mu_2)=\alpha\, d\big(\mu_1,\alpha\mu_1+(1-\alpha)\mu_2\big)+(1-\alpha)\, d\big(\mu_2,\alpha\mu_1+(1-\alpha)\mu_2\big).$$
--   6. For $a\in\{2,\dots,K\}$, $g_a(x)=(1+x)\,I_{\frac1{1+x}}(\mu_1,\mu_a)$, and $x_a(y)=g_a^{-1}(y)$ is the inverse of $g_a$ on $[0,+\infty[$; $x_1$ is the function constantly equal to $1$.
--   7. Finally
--   $$F_{\boldsymbol\mu}(y)=\sum_{a=2}^K\frac{d\Big(\mu_1,\frac{\mu_1+x_a(y)\mu_a}{1+x_a(y)}\Big)}{d\Big(\mu_a,\frac{\mu_1+x_a(y)\mu_a}{1+x_a(y)}\Big)}.$$
--
--   These are the objects of the optimization problem (1) of the paper and of its explicit solution (Lemma 3, Lemma 4, Theorem 5).
--
--   **Formalization Note** Arms are $0,\dots,K-1$; the paper's arm $1$ is index $0$ and the paper's arms $2,\dots,K$ are the indices $\ne 0$. $\mathrm{Alt}(\boldsymbol\mu)$ is encoded as the models of $\mathcal S$ whose optimal arm is not an optimal arm of $\boldsymbol\mu$ (the paper's definition when $\boldsymbol\mu\in\mathcal S$). The transportation cost is an infimum in the extended reals, so it is the true infimum (an empty set would give $+\infty$, never a default $0$). $w^*(\boldsymbol\mu)$ is not defined by choice: "$w$ is optimal" is a predicate. $I_\alpha$ is defined for every real $\alpha$ but only used for $\alpha\in[0,1]$. $x_a$ is the inverse chosen on $[0,+\infty[$; outside the range of $g_a$ its value is an unspecified default, and the theorems only evaluate it on $[0,d(\mu_1,\mu_2)[$.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 3 (§2.1: S, Alt, Σ_K), p. 4 (eq. (1), w*, S), p. 5 (§2.2: eq. (3), eq. (4), x_a, eq. (6))

import Mathlib
import Definitions.Def_OptimalBAI_OptProportions_ExpFamily

namespace OptimalBAI.OptProportions

variable {K : ℕ}

/-- Arm `a` is the unique optimal arm of the mean vector `μ`: `μ_a > μ_i` for every `i ≠ a`. -/
def IsBest (μ : Fin K → ℝ) (a : Fin K) : Prop :=
  ∀ i, i ≠ a → μ i < μ a

/-- The class `𝒮` of exponential-family bandit models with a unique optimal arm (paper, p. 4):
mean vectors `λ = (λ_1, …, λ_K)` with every `λ_a` in the mean space `ḃ(Θ)` and some arm strictly
better than all others. -/
def bestArmModels (F : ExpFamily) (K : ℕ) : Set (Fin K → ℝ) :=
  {lam | (∀ a, lam a ∈ F.M) ∧ ∃ a, IsBest lam a}

/-- `Alt(μ) = {λ ∈ 𝒮 : a*(λ) ≠ a*(μ)}` (paper, p. 3): the models of `𝒮` whose optimal arm is not an
optimal arm of `μ`. -/
def Alt (F : ExpFamily) (μ : Fin K → ℝ) : Set (Fin K → ℝ) :=
  {lam | lam ∈ bestArmModels F K ∧ ∀ a, IsBest lam a → ¬ IsBest μ a}

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

/-- The parameterized Jensen–Shannon divergence, eq. (3), p. 5:
`I_α(μ₁, μ₂) = α d(μ₁, αμ₁ + (1-α)μ₂) + (1-α) d(μ₂, αμ₁ + (1-α)μ₂)`, for `α ∈ [0, 1]`. -/
noncomputable def jensenShannon (F : ExpFamily) (α μ₁ μ₂ : ℝ) : ℝ :=
  α * F.d μ₁ (α * μ₁ + (1 - α) * μ₂) + (1 - α) * F.d μ₂ (α * μ₁ + (1 - α) * μ₂)

/-- `g_a(x) = (1 + x) I_{1/(1+x)}(μ_1, μ_a)`, eq. (4), p. 5 (arm `1` of the paper is index `0`). -/
noncomputable def gFun [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (a : Fin K) (x : ℝ) : ℝ :=
  (1 + x) * jensenShannon F (1 / (1 + x)) (μ 0) (μ a)

/-- `x_a(y)`, p. 5: for `a ≠ 1` (index `≠ 0`), the inverse of `g_a` on `[0, +∞[`,
`x_a(y) = g_a⁻¹(y)`; `x_1` is the function constantly equal to `1`. (For `y` outside the range of
`g_a` on `[0, +∞[` the value is an unspecified junk value; the statements only evaluate `x_a` on
`[0, d(μ_1, μ_a)[`.) -/
noncomputable def xFun [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (a : Fin K) (y : ℝ) : ℝ :=
  if a = 0 then 1 else Function.invFunOn (gFun F μ a) (Set.Ici 0) y

/-- `F_μ(y) = ∑_{a=2}^K d(μ_1, (μ_1 + x_a(y) μ_a)/(1 + x_a(y))) / d(μ_a, (μ_1 + x_a(y) μ_a)/(1 + x_a(y)))`,
eq. (6), p. 5 (arms `2, …, K` of the paper are the indices `≠ 0`). -/
noncomputable def FFun [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ) (y : ℝ) : ℝ :=
  ∑ a ∈ Finset.univ.erase (0 : Fin K),
    F.d (μ 0) ((μ 0 + xFun F μ a y * μ a) / (1 + xFun F μ a y)) /
      F.d (μ a) ((μ 0 + xFun F μ a y * μ a) / (1 + xFun F μ a y))

end OptimalBAI.OptProportions


