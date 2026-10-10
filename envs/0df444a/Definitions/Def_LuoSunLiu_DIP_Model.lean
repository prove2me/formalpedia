-- Prove2me | Definitions.Def_LuoSunLiu_DIP_Model
-- name    : LuoSunLiu_DIP_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:14:06.479987+00:00
-- url     : https://prove2.me/theorems/2137cd11-c1c9-406d-95e8-c4e00eb17804
-- title:
--   §2.1, pp. 6–7 — linear valuation with unknown noise CDF F, revenue f_q, clairvoyant price p*, regret (1)
-- statement:
--   This file sets up the contextual dynamic pricing model of Luo, Sun and Liu (§2.1).
--
--   At each period $t = 1, 2, \dots$ a customer with covariate $x_t \in \mathcal X \subseteq \mathbb R^{d_0}$ arrives, where $\|x\|_\infty \le 1$ for every $x \in \mathcal X$. Their valuation is $v_t = x_t^\top\theta_0 + z_t$, with an unknown parameter $\theta_0$, $\|\theta_0\|_1 \le W$ for a known $W$, and market noises $z_t$ drawn i.i.d. from an unknown CDF $F$. The seller posts a price $p_t$ and observes $y_t = \mathbf 1\{v_t \ge p_t\}$; the reward is $Z_t = p_t y_t$. Prices are bounded by a known $p_{\max} > 0$.
--
--   1. The **ℓ₁ norm** $\|v\|_1 = \sum_i |v_i|$.
--   2. The **expected revenue** of price $p$ at linear value $q = x^\top\theta_0$:
--   $$f_q(p) = p\,\bigl(1 - F(p - q)\bigr).$$
--   3. A **pricing model** bundles $\theta_0, W, p_{\max}, \mathcal X, F$ and a clairvoyant price function $p^*$. Its **standing assumptions** are $\|\theta_0\|_1 \le W$, $p_{\max} > 0$, $\|x\|_\infty \le 1$ on $\mathcal X$, and, for every $x \in \mathcal X$, $p^*(x) \in (0, p_{\max})$ and $f_{x^\top\theta_0}(p) \le f_{x^\top\theta_0}(p^*(x))$ for all $p > 0$ (that is, $p^*(x) \in \arg\max_{p>0} f_{x^\top\theta_0}(p)$).
--   4. The **per-period regret** (1):
--   $$r_t = f_{x_t^\top\theta_0}(p^*_t) - f_{x_t^\top\theta_0}(p_t), \qquad p^*_t = p^*(x_t).$$
--   5. **Assumption 2** with constant $C$: $f_q(p^*(x)) - f_q(p) \le C\,(p^*(x) - p)^2$ for all $x \in \mathcal X$, $q = x^\top\theta_0$ and $p \in [0, p_{\max}]$.
--   6. The **stochastic primitives** on a probability space with a filtration $(\mathcal G_t)$: for every $t \ge 1$, $x_t$ and $p_t$ are $\mathcal G_{t-1}$-measurable, $x_t \in \mathcal X$, the noise $z_t$ is $\mathcal G_t$-measurable, has CDF $F$, and is independent of $\mathcal G_{t-1}$.
--   7. The **response** $y_t = \mathbf 1\{p_t \le x_t^\top\theta_0 + z_t\}$.
--
--   These objects are shared by every statement of the mission: the single-episode results (Lemma 1, Propositions 3–4) and the main Theorem 1.
--
--   **Formalization Note** The filtration $\mathcal G$ generalizes the paper's $\sigma(x_1, p_1, Z_1, \dots, x_t, p_t)$ (proof of Lemma 1, p. 35): it may contain independent randomization and adversarially chosen covariates. Independence of $z_t$ from $\mathcal G_{t-1}$ together with the common CDF makes the $z_t$ i.i.d. The condition $p^*(x) \in (0, p_{\max})$ is the paper's assumption from the proof of Proposition 1 (p. 51), used in Proposition 3 (p. 53). The value of $r_t$ does not depend on which maximizer $p^*(x)$ is chosen. Periods are 1-based; index $0$ of every process is unused.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, pp. 6–7, §2.1 and (1); p. 9 (W); p. 10 (p_max); p. 18, f_q and Assumption 2; p. 51 (p*(x) ∈ (0, p_max)); proof of Lemma 1, pp. 34–35 (filtration)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace LuoSunLiu.DIP

/-- The ℓ₁ norm `‖v‖₁ = ∑ᵢ |vᵢ|` of a vector (the default norm on `Fin n → ℝ` is the sup norm,
so the ℓ₁ norm is written out). -/
noncomputable def l1 {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, |v i|

/-- The expected revenue `f_q(p) = p (1 - F(p - q))` of posting price `p` to a customer whose
linear valuation component is `q = xᵀθ₀` (Luo, Sun and Liu, arXiv:2109.07340v2, p. 7 and p. 18). -/
def revenue (F : ℝ → ℝ) (q p : ℝ) : ℝ := p * (1 - F (p - q))

/-- The data of the contextual pricing model of §2.1 (pp. 6–7): covariates in `X ⊆ ℝ^{d₀}`, the
unknown parameter `θ₀`, its known ℓ₁ bound `W`, the known price bound `p_max`, the noise CDF `F`,
and a clairvoyant price function `p*`. -/
structure PricingModel (d0 : ℕ) where
  /-- the true linear parameter `θ₀` -/
  θ0 : Fin d0 → ℝ
  /-- the known bound `W` on `‖θ₀‖₁` (p. 9) -/
  W : ℝ
  /-- the known price bound `p_max` (p. 10) -/
  pmax : ℝ
  /-- the covariate space `𝒳` -/
  X : Set (Fin d0 → ℝ)
  /-- the CDF `F` of the market noise -/
  F : ℝ → ℝ
  /-- a clairvoyant (optimal) price `p*(x)` -/
  pstar : (Fin d0 → ℝ) → ℝ

/-- The standing assumptions of §2.1 on the model data: `‖θ₀‖₁ ≤ W` (p. 9), `p_max > 0` (p. 10),
`‖x‖_∞ ≤ 1` for every `x ∈ 𝒳` (p. 6), and for every `x ∈ 𝒳` the price `p*(x)` lies in
`(0, p_max)` (p. 51) and maximizes `p ↦ f_{xᵀθ₀}(p)` over all `p > 0` (p. 7). -/
def PricingModel.Standing {d0 : ℕ} (M : PricingModel d0) : Prop :=
  l1 M.θ0 ≤ M.W ∧ 0 < M.pmax ∧ (∀ x ∈ M.X, ∀ i, |x i| ≤ 1) ∧
    ∀ x ∈ M.X, M.pstar x ∈ Set.Ioo 0 M.pmax ∧
      ∀ p : ℝ, 0 < p → revenue M.F (x ⬝ᵥ M.θ0) p ≤ revenue M.F (x ⬝ᵥ M.θ0) (M.pstar x)

/-- The per-period regret (1), p. 7: `r = p*(x)(1 - F(p*(x) - xᵀθ₀)) - p(1 - F(p - xᵀθ₀))`. Its
value does not depend on which maximizer `p*(x)` is chosen. -/
def perRegret {d0 : ℕ} (M : PricingModel d0) (x : Fin d0 → ℝ) (p : ℝ) : ℝ :=
  revenue M.F (x ⬝ᵥ M.θ0) (M.pstar x) - revenue M.F (x ⬝ᵥ M.θ0) p

/-- Assumption 2 (p. 18) with constant `C`: for every `x ∈ 𝒳` and `q = xᵀθ₀`,
`f_q(p*(x)) - f_q(p) ≤ C (p*(x) - p)²` for all `p ∈ [0, p_max]`. -/
def Assumption2 {d0 : ℕ} (M : PricingModel d0) (C : ℝ) : Prop :=
  ∀ x ∈ M.X, ∀ p ∈ Set.Icc 0 M.pmax,
    revenue M.F (x ⬝ᵥ M.θ0) (M.pstar x) - revenue M.F (x ⬝ᵥ M.θ0) p ≤ C * (M.pstar x - p) ^ 2

/-- The stochastic primitives of the pricing model (§2.1, pp. 6–7; proof of Lemma 1, pp. 34–35),
with periods `t = 1, 2, …` and a filtration `𝒢` (index `0` unused for the processes):
* the covariate `x_t ∈ 𝒳` and the price `p_t` are `𝒢_{t-1}`-measurable (they may depend on all
  past data and on independent randomization; covariates may be chosen adversarially);
* the noise `z_t` is `𝒢_t`-measurable, has CDF `F` (`P(z_t ≤ c) = F(c)` for every `c`), and is
  independent of `𝒢_{t-1}` (so the `z_t` are i.i.d. with CDF `F`). -/
def IsPricingEnv {d0 : ℕ} (M : PricingModel d0) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (𝒢 : Filtration ℕ mΩ) (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    Measurable[𝒢 (t - 1)] (x t) ∧ Measurable[𝒢 (t - 1)] (p t) ∧ Measurable[𝒢 t] (z t) ∧
    (∀ ω, x t ω ∈ M.X) ∧
    (∀ c : ℝ, P.real {ω | z t ω ≤ c} = M.F c) ∧
    Indep (MeasurableSpace.comap (z t) inferInstance) (𝒢 (t - 1)) P

/-- The binary purchase response `y_t = 1{v_t ≥ p_t}` with valuation `v_t = x_tᵀθ₀ + z_t`
(pp. 6–7), as a real number in `{0, 1}`. The reward is `Z_t = p_t y_t`. -/
noncomputable def response {d0 : ℕ} (M : PricingModel d0) {Ω : Type*}
    (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if p t ω ≤ x t ω ⬝ᵥ M.θ0 + z t ω then 1 else 0

end LuoSunLiu.DIP


