-- Prove2me | Definitions.Def_SalesRebate_NoIncreasing_Setting
-- name    : SalesRebate_NoIncreasing_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:02:37.537881+00:00
-- url     : https://prove2.me/theorems/65513438-9238-4cb8-8e2b-9a601ceff40c
-- title:
--   §II, pp. 6–10 (PDF 6–10) — Gaussian quality and tastes, posterior, reward program and r̂, equilibrium cutoff (1), expected profit (2), Assumption 1, profitable
-- statement:
--   This file fixes the model of §II of Ajorlou and Jadbabaie's *Sales-Based Rebate Design*.
--
--   A firm sells a product at a market price $p$ to a unit mass of consumers. Consumer $i$ values the product at $v_i = v + \epsilon_i$, where the common quality $v$ has the Gaussian prior $v \sim N(\theta, \sigma_\theta^2)$ and the idiosyncratic taste is $\epsilon_i \sim N(0, \sigma_\epsilon^2)$. A **model** is the triple $(\theta, \sigma_\theta, \sigma_\epsilon)$; it is **valid** when $\sigma_\theta > 0$ and $\sigma_\epsilon > 0$. Write
--   $$\sigma^2 = \sigma_\epsilon^2 + \sigma_\theta^2, \qquad \tau = \frac{\sigma_\theta^2}{\sigma_\epsilon^2 + \sigma_\theta^2}, \qquad \sigma_v^2 = \frac{\sigma_\epsilon^2 \sigma_\theta^2}{\sigma_\epsilon^2 + \sigma_\theta^2}.$$
--
--   The objects defined are:
--
--   1. the **posterior** of the quality given a valuation $v_i = x$: $v \mid v_i = x \sim N(\tau x + (1-\tau)\theta, \sigma_v^2)$, and the **expected reward** $\mathbb E_{v\mid v_i = x}[\hat r(v)] = \int \hat r \, dN(\tau x + (1-\tau)\theta, \sigma_v^2)$ of a reward $\hat r$ (a function of the quality);
--   2. the **sales volume** $\bar a = \Phi((v-c)/\sigma_\epsilon)$ at quality $v$ when consumers buy iff $v_i > c$, with $\Phi$ the standard normal CDF;
--   3. a **reward program** $r : [0,1] \to [0,p]$ (a function of the sales volume), and the induced reward as a function of the quality, $\hat r(v) = r(\Phi((v-c)/\sigma_\epsilon))$;
--   4. the **equilibrium cutoff** condition (1): the threshold strategy $a_i = \mathbf 1\{v_i > c\}$ is an equilibrium for $\hat r$ at price $p$ iff $\mathbb E_{v\mid v_i}[\hat r(v)] + v_i - p \ge 0$ for $v_i \ge c$ and $\le 0$ for $v_i \le c$;
--   5. the firm's **expected profit** (2): $\mathbb E_v[\Pi(p, \hat r)] = \mathbb E_v[(p - \hat r(v))\Phi((v-c)/\sigma_\epsilon)]$, the expectation over the prior;
--   6. the ex-ante **density of a valuation** $\psi(x) = \phi((\theta - x)/\sigma)/\sigma$, with $\phi$ the standard normal density;
--   7. **Assumption 1** (maximization clause): $p$ maximizes the no-reward ex-ante profit $x\Phi((\theta - x)/\sigma)$ over prices $x \ge 0$;
--   8. **profitable**: the reward program $r$ with equilibrium cutoff $c$ yields an expected profit strictly above that of the no-reward case at the price $p$, i.e. (2) with $\hat r \equiv 0$ and cutoff $p$.
--
--   These are the objects every statement of the mission is posed on.
--
--   **Formalization Note** $\Phi$ and $\phi$ are the published `BlackScholesModel.stdNormalCDF` and `stdNormalPDF`. Variances enter `gaussianReal` through `Real.toNNReal`, which is exact under validity. The positivity of $\sigma_\theta, \sigma_\epsilon$ is implicit on the page (Gaussian laws, divisions by $\sigma_\epsilon$ and $\sigma$) and is stated explicitly. A reward program is a function `ℝ → ℝ` constrained only on $[0,1]$; its values elsewhere never matter because $\Phi$ takes values in $(0,1)$. The prior on p. 9 is misprinted as $N(\theta, \sigma_v^2)$; the prior used is $N(\theta, \sigma_\theta^2)$ from p. 6. The uniqueness/first-order-condition clause of Assumption 1 is not encoded.
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, pp. 6–10, §II (model p. 6, reward program and σ² p. 7, Assumption 1 and 'profitable' p. 8, posterior and (1) p. 9, (2) and r̂ p. 10); ψ p. 16

import Mathlib
import Definitions.Def_BlackScholesModel_Core

namespace SalesRebate.NoIncreasing

open MeasureTheory ProbabilityTheory BlackScholesModel

/-- §II, p. 6: the prior mean `θ` of the common quality `v ∼ N(θ, σθ²)`, its standard
deviation `σθ`, and the standard deviation `σε` of the idiosyncratic taste `εᵢ ∼ N(0, σε²)`. -/
structure Model where
  θ : ℝ
  σθ : ℝ
  σε : ℝ

/-- The standing assumptions of §II: both Gaussian laws are non-degenerate. -/
structure Model.Valid (M : Model) : Prop where
  σθ_pos : 0 < M.σθ
  σε_pos : 0 < M.σε

/-- p. 7: `σ = √(σε² + σθ²)`, the standard deviation of a valuation `vᵢ ∼ N(θ, σ²)`. -/
noncomputable def Model.σ (M : Model) : ℝ := Real.sqrt (M.σε ^ 2 + M.σθ ^ 2)

/-- p. 9: `τ = σθ² / (σε² + σθ²)`. -/
noncomputable def Model.tau (M : Model) : ℝ := M.σθ ^ 2 / (M.σε ^ 2 + M.σθ ^ 2)

/-- p. 9: `σv² = σε² σθ² / (σε² + σθ²)`, the posterior variance of the quality. -/
noncomputable def Model.σv2 (M : Model) : ℝ := M.σε ^ 2 * M.σθ ^ 2 / (M.σε ^ 2 + M.σθ ^ 2)

/-- p. 6: the prior law `N(θ, σθ²)` of the common quality `v`. -/
noncomputable def Model.prior (M : Model) : Measure ℝ := gaussianReal M.θ (M.σθ ^ 2).toNNReal

/-- p. 9: the posterior mean `τ x + (1 − τ) θ` of the quality given the valuation `vᵢ = x`. -/
noncomputable def Model.postMean (M : Model) (x : ℝ) : ℝ := M.tau * x + (1 - M.tau) * M.θ

/-- p. 9: the posterior law `v | vᵢ = x ∼ N(τ x + (1 − τ) θ, σv²)`. -/
noncomputable def Model.posterior (M : Model) (x : ℝ) : Measure ℝ :=
  gaussianReal (M.postMean x) M.σv2.toNNReal

/-- The reward a consumer with valuation `x` expects, `E_{v|vᵢ=x}[r̂(v)]`. -/
noncomputable def Model.condReward (M : Model) (rhat : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ v, rhat v ∂(M.posterior x)

/-- pp. 7, 9: the sales volume `ā = Φ((v − c)/σε)` at quality `v` under the cutoff `c`. -/
noncomputable def Model.salesVolume (M : Model) (c v : ℝ) : ℝ := stdNormalCDF ((v - c) / M.σε)

/-- p. 10: `r̂(v) = r(Φ((v − c)/σε))`, the reward as a function of the quality. -/
noncomputable def Model.rhat (M : Model) (r : ℝ → ℝ) (c v : ℝ) : ℝ := r (M.salesVolume c v)

/-- (1), p. 9: the threshold strategy `aᵢ = 1{vᵢ > c}` is an equilibrium strategy at price `p`
for the reward `r̂`. -/
def Model.IsEquilibriumCutoff (M : Model) (p : ℝ) (rhat : ℝ → ℝ) (c : ℝ) : Prop :=
  (∀ x, c ≤ x → 0 ≤ M.condReward rhat x + x - p) ∧
    (∀ x, x ≤ c → M.condReward rhat x + x - p ≤ 0)

/-- (2), p. 10: the firm's expected profit `E_v[(p − r̂(v)) Φ((v − c)/σε)]`. -/
noncomputable def Model.expectedProfit (M : Model) (p : ℝ) (rhat : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∫ v, (p - rhat v) * M.salesVolume c v ∂M.prior

/-- p. 16: `ψ(x) = φ((θ − x)/σ)/σ`, the ex-ante density of a valuation. -/
noncomputable def Model.psi (M : Model) (x : ℝ) : ℝ := stdNormalPDF ((M.θ - x) / M.σ) / M.σ

/-- Assumption 1, p. 8 (maximization clause): the market price `p` maximizes the ex-ante
expected no-reward profit `x Φ((θ − x)/σ)` over prices `x ≥ 0`. -/
def Model.IsMarketPrice (M : Model) (p : ℝ) : Prop :=
  ∀ x, 0 ≤ x → x * stdNormalCDF ((M.θ - x) / M.σ) ≤ p * stdNormalCDF ((M.θ - p) / M.σ)

/-- p. 7: `r` is a reward program `[0, 1] → [0, p]` (a function of the sales volume). -/
def IsRewardProgram (p : ℝ) (r : ℝ → ℝ) : Prop := ∀ a ∈ Set.Icc (0 : ℝ) 1, r a ∈ Set.Icc 0 p

/-- p. 8: the reward program `r` with equilibrium cutoff `c` is profitable: its expected
profit (2) exceeds that of the no-reward case at the market price `p` (reward `0`, cutoff `p`). -/
def Model.IsProfitable (M : Model) (p : ℝ) (r : ℝ → ℝ) (c : ℝ) : Prop :=
  M.expectedProfit p (fun _ => 0) p < M.expectedProfit p (M.rhat r c) c

end SalesRebate.NoIncreasing


