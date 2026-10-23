-- Prove2me | Definitions.Def_MostlyExplorationFree_GreedyBandit_Model
-- name    : MostlyExplorationFree_GreedyBandit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:27.674029+00:00
-- url     : https://prove2.me/theorems/700de66c-395f-4417-94f2-2079ce96d4d8
-- title:
--   §2–§3.1, pp. 7–12 — two-armed linear contextual bandit, Assumptions 1–3, OLS (Definition 3), the Greedy Bandit (Algorithm 1) and its regret
-- statement:
--   The two-armed linear contextual bandit and the Greedy Bandit algorithm of Bastani, Bayati and Khosravi.
--
--   **Model.** There are two arms $i \in \{1, 2\}$ with unknown parameters $\beta_1, \beta_2 \in \mathbb R^d$. At each time $t = 1, 2, \dots$ a context $X_t \in \mathbb R^d$ is observed; the contexts are i.i.d. with law $P_X$. Pulling arm $i$ at time $t$ yields the reward $Y_{i,t} = X_t^\top \beta_i + \varepsilon_{i,t}$, where the noises $\varepsilon_{i,t}$ are independent, mean-zero and $\sigma$-sub-Gaussian: $\mathbb E[e^{\tau \varepsilon_{i,t}}] \le e^{\tau^2\sigma^2/2}$ for every real $\tau$. Ties are broken by fair coins $W_t$. Contexts, noises and coins are mutually independent.
--
--   **Assumptions.**
--   1. *Parameter set*: $x_{\max} > 0$, $\|X_t\|_2 \le x_{\max}$ almost surely, and $\|\beta_i\|_2 \le b_{\max}$.
--   2. *Margin condition*: there is $C_0 > 0$ with $P_X[0 < |X^\top(\beta_i - \beta_j)| \le \kappa] \le C_0 \kappa$ for all $i \ne j$ and $\kappa > 0$.
--   3. *Covariate diversity*: there is $\lambda_0 > 0$ such that for every $u \in \mathbb R^d$,
--   $$
--   \lambda_{\min}\big(\mathbb E_X[X X^\top \mathbb I\{X^\top u \ge 0\}]\big) \ge \lambda_0 .
--   $$
--
--   **Greedy Bandit (Algorithm 1).** Let $\mathcal S_{i,t} = \{s \in [1,t] : \pi_s = i\}$ be the times up to $t$ at which arm $i$ was pulled, $\hat\Sigma(\mathcal S_{i,t}) = \sum_{s \in \mathcal S_{i,t}} X_s X_s^\top$ its sample covariance matrix, and
--   $$
--   \hat\beta(\mathcal S_{i,t}) = \hat\Sigma(\mathcal S_{i,t})^{-1} \sum_{s \in \mathcal S_{i,t}} Y_{\pi_s, s} X_s
--   $$
--   the ordinary least squares estimate when $\hat\Sigma(\mathcal S_{i,t})$ is invertible, and $0$ otherwise. At time $t$ the algorithm pulls $\pi_t = \arg\max_i X_t^\top \hat\beta(\mathcal S_{i,t-1})$, breaking a tie with the coin $W_t$.
--
--   **Regret.** The instantaneous expected regret and the cumulative expected regret are
--   $$
--   r_t = \mathbb E\Big[\max_{j} X_t^\top \beta_j - X_t^\top \beta_{\pi_t}\Big], \qquad R_T = \sum_{t=1}^T r_t .
--   $$
--
--   **Constants.** $\bar C = \tfrac13 + \tfrac72(\log d)^{-1/2} + \tfrac{38}{3}(\log d)^{-1} + \tfrac{67}{4}(\log d)^{-3/2}$ (display (4)), $C_1 = \lambda_0/(40x_{\max}^2)$, $C_2 = \lambda^2/(2d\sigma^2x_{\max}^2)$ and $C_3 = \lambda_0^2/(32d\sigma^2x_{\max}^2)$.
--
--   This is the model of the paper's main result (Theorem 1): under covariate diversity the purely greedy policy, which never explores, has logarithmic regret.
--
--   **Formalization Note**
--   1. Arms are `Fin 2` (the paper's arm 1 is `0`, arm 2 is `1`); times are natural numbers starting at `1`, and the slots `t = 0` of the random sequences are unused.
--   2. The paper's Definition 1 asks the moment-generating-function bound only for $\tau > 0$, which does not even force mean zero; the two-sided form (Mathlib's `HasSubgaussianMGF`) is used, as the proofs require.
--   3. The paper assumes the context law has a Lebesgue density; no step of Theorem 1's proof uses it, so the context law is an arbitrary probability measure $\mu$ (a disclosed generalisation).
--   4. Algorithm 1 updates an arm's estimate only when its Gram matrix is invertible and starts from $0$. Gram matrices only grow, so a matrix singular at time $t$ was singular at every earlier update; the closed form "OLS if invertible, else $0$" is therefore the stored value.
--   5. The run is defined by strong recursion on $t$ as a function of the realised contexts, noises and coins; the expectation in $r_t$ is over all of them. Its integrand is bounded by $2x_{\max}b_{\max}$ almost surely under Assumption 1.
--   6. $\bar C$ uses real powers of $\log d$, which take junk values at $d \le 1$; every statement using it assumes $d \ge 2$.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, pp. 7–12, §2 (model p. 7, Definition 1 p. 7, regret p. 7, Assumptions 1–2 p. 8, Assumption 3 p. 9), §3 (notation and Definition 3 p. 11, Algorithm 1 p. 12, display (4) p. 12), constants C₁ (Lemma 4, p. 14), C₂ (Lemma 5, p. 15), C₃ (Lemma 6, p. 16)

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Matrix

namespace MostlyExplorationFree.GreedyBandit

open Matrix MeasureTheory ProbabilityTheory

/-! ## Assumptions 1–3 (pp. 8–9)

Arms are `Fin 2`: the paper's arm 1 is `0`, arm 2 is `1`. -/

/-- **Assumption 1 (Parameter Set)**: `x_max > 0`, contexts lie in the closed ℓ₂ ball of radius
`x_max` almost surely, and every arm parameter has ℓ₂ norm at most `b_max`. -/
def ParameterSet {d : ℕ} (μ : Measure (Fin d → ℝ)) (β : Fin 2 → Fin d → ℝ) (xmax bmax : ℝ) :
    Prop :=
  0 < xmax ∧ (∀ᵐ x ∂μ, l2norm x ≤ xmax) ∧ ∀ i, l2norm (β i) ≤ bmax

/-- **Assumption 2 (Margin Condition)**: there is `C₀ > 0` with
`P_X[0 < |Xᵀ(βᵢ − βⱼ)| ≤ κ] ≤ C₀ κ` for all `i ≠ j` and all `κ > 0`. -/
def MarginCondition {d : ℕ} (μ : Measure (Fin d → ℝ)) (β : Fin 2 → Fin d → ℝ) (C0 : ℝ) : Prop :=
  0 < C0 ∧ ∀ i j : Fin 2, i ≠ j → ∀ κ : ℝ, 0 < κ →
    μ {x | 0 < |x ⬝ᵥ (β i - β j)| ∧ |x ⬝ᵥ (β i - β j)| ≤ κ} ≤ ENNReal.ofReal (C0 * κ)

/-- The matrix `E_X[X Xᵀ 𝕀{Xᵀu ≥ 0}]`, entrywise as a Bochner integral against the context law. -/
noncomputable def halfSpaceSecondMoment {d : ℕ} (μ : Measure (Fin d → ℝ)) (u : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b => ∫ x, Set.indicator {y : Fin d → ℝ | 0 ≤ y ⬝ᵥ u} (fun y => y a * y b) x ∂μ

/-- **Assumption 3 (Covariate Diversity)**: there is `λ₀ > 0` such that for every `u ∈ ℝ^d`,
`λ_min(E_X[X Xᵀ 𝕀{Xᵀu ≥ 0}]) ≥ λ₀`. -/
def CovariateDiversity {d : ℕ} (μ : Measure (Fin d → ℝ)) (lam0 : ℝ) : Prop :=
  0 < lam0 ∧ ∀ u : Fin d → ℝ, lam0 ≤ lambdaMin (halfSpaceSecondMoment μ u)

/-! ## The probability model (p. 7) -/

/-- Indices of the primitive random variables of the model: contexts `X_t` (`t ≥ 1`),
noises `ε_{i,t}` (`t ≥ 1`) and tie-breaking coins `W_t` (`t ≥ 1`). The index `t` stands for
time `t + 1`. -/
abbrev ModelIndex := (ℕ ⊕ (Fin 2 × ℕ)) ⊕ ℕ

/-- The σ-algebra generated by each primitive random variable of the model. -/
@[instance_reducible] def modelSigma {Ω : Type*} {d : ℕ} (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) : ModelIndex → MeasurableSpace Ω :=
  Sum.elim
    (Sum.elim (fun t => MeasurableSpace.comap (X (t + 1)) inferInstance)
      (fun p => MeasurableSpace.comap (ε p.1 (p.2 + 1)) inferInstance))
    (fun t => MeasurableSpace.comap (W (t + 1)) inferInstance)

/-- The standing probability model of §2 on a probability space `(Ω, P)`:
* contexts `X_t`, `t ≥ 1`, are i.i.d. with law `μ`;
* noises `ε_{i,t}`, `t ≥ 1`, are mean-zero sub-Gaussian with variance proxy `σ²`
  (two-sided moment-generating-function bound);
* tie-breaking coins `W_t`, `t ≥ 1`, are fair;
* all of these random variables are mutually independent.
The slots `t = 0` are unused. -/
structure IsGreedyModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (σ : ℝ) : Prop where
  isProbability : IsProbabilityMeasure P
  measurable_X : ∀ t, Measurable (X t)
  law_X : ∀ t, 1 ≤ t → P.map (X t) = μ
  measurable_ε : ∀ i t, Measurable (ε i t)
  subgaussian_ε : ∀ i t, 1 ≤ t → HasSubgaussianMGF (ε i t) (σ ^ 2).toNNReal P
  measurable_W : ∀ t, Measurable (W t)
  fair_W : ∀ t, 1 ≤ t → P {ω | W t ω = true} = 2⁻¹
  indep : iIndep (modelSigma X ε W) P

/-! ## The Greedy Bandit (Algorithm 1, p. 12)

The run is a deterministic function of one realisation `(x, e, w)` of contexts, noises and coins.
`a : ℕ → Fin 2` stands for the sequence of arms played; only its values at times `≤ t` matter
for the quantities at time `t`. -/

/-- `S_{i,t} = {s ∈ [1, t] : π_s = i}` for an arm sequence `a`. -/
def playedOf (a : ℕ → Fin 2) (i : Fin 2) (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).filter (fun s => a s = i)

/-- `Σ̂(S_{i,t}) = X(S_{i,t})ᵀ X(S_{i,t}) = ∑_{s ∈ S_{i,t}} X_s X_sᵀ`. -/
def gramOf {d : ℕ} (x : ℕ → Fin d → ℝ) (a : ℕ → Fin 2) (i : Fin 2) (t : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ s ∈ playedOf a i t, Matrix.vecMulVec (x s) (x s)

/-- The observed reward `Y_{π_s,s} = X_sᵀ β_{π_s} + ε_{π_s,s}` at time `s`. -/
def rewardOf {d : ℕ} (β : Fin 2 → Fin d → ℝ) (x : ℕ → Fin d → ℝ) (e : Fin 2 → ℕ → ℝ)
    (a : ℕ → Fin 2) (s : ℕ) : ℝ :=
  x s ⬝ᵥ β (a s) + e (a s) s

/-- The stored estimate `β̂(S_{i,t})` of Algorithm 1: the OLS estimator (Definition 3)
`(X(S)ᵀX(S))⁻¹ X(S)ᵀ Y(S)` on `S = S_{i,t}` when `X(S)ᵀX(S)` is invertible (nonzero determinant), and the initial
value `0` otherwise. -/
noncomputable def estOf {d : ℕ} (β : Fin 2 → Fin d → ℝ) (x : ℕ → Fin d → ℝ)
    (e : Fin 2 → ℕ → ℝ) (a : ℕ → Fin 2) (i : Fin 2) (t : ℕ) : Fin d → ℝ :=
  if (gramOf x a i t).det ≠ 0 then
    (gramOf x a i t)⁻¹ *ᵥ ∑ s ∈ playedOf a i t, rewardOf β x e a s • x s
  else 0

/-- The greedy decision at time `t` given the estimates `b₀ = β̂(S_{1,t−1})`,
`b₁ = β̂(S_{2,t−1})`: arm 1 (`0`) if `xᵀb₀ > xᵀb₁`, arm 2 (`1`) if `xᵀb₀ < xᵀb₁`, and on a tie
arm 1 if the coin shows `true`, arm 2 otherwise. -/
noncomputable def greedyChoice {d : ℕ} (xt : Fin d → ℝ) (b0 b1 : Fin d → ℝ) (wt : Bool) : Fin 2 :=
  if xt ⬝ᵥ b1 < xt ⬝ᵥ b0 then 0
  else if xt ⬝ᵥ b0 < xt ⬝ᵥ b1 then 1
  else if wt then 0 else 1

/-- The arms `π_t` played by the Greedy Bandit on the realisation `(x, e, w)`, by strong
recursion on `t`: `π_t` is the greedy choice for `x t` against the estimates built from the
arms `π_s`, `s < t` (the value at `t = 0` is an unused placeholder). -/
noncomputable def armSeq {d : ℕ} (β : Fin 2 → Fin d → ℝ) (x : ℕ → Fin d → ℝ)
    (e : Fin 2 → ℕ → ℝ) (w : ℕ → Bool) : ℕ → Fin 2 :=
  Nat.strongRec fun t ih =>
    greedyChoice (x t)
      (estOf β x e (fun s => if h : s < t then ih s h else 0) 0 (t - 1))
      (estOf β x e (fun s => if h : s < t then ih s h else 0) 1 (t - 1)) (w t)

section Run

variable {Ω : Type*} {d : ℕ} (β : Fin 2 → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ)
  (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)

/-- `π_t(ω)`: the arm the Greedy Bandit pulls at time `t ≥ 1`. -/
noncomputable def arm (t : ℕ) (ω : Ω) : Fin 2 :=
  armSeq β (fun s => X s ω) (fun i s => ε i s ω) (fun s => W s ω) t

/-- `S_{i,t}(ω)`: the times `s ∈ [1, t]` at which arm `i` was pulled. -/
noncomputable def played (i : Fin 2) (t : ℕ) (ω : Ω) : Finset ℕ :=
  playedOf (fun s => arm β X ε W s ω) i t

/-- `Σ̂(S_{i,t})(ω) = X(S_{i,t})ᵀ X(S_{i,t})`, the sample covariance matrix of arm `i`. -/
noncomputable def gram (i : Fin 2) (t : ℕ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  gramOf (fun s => X s ω) (fun s => arm β X ε W s ω) i t

/-- `β̂(S_{i,t})(ω)`: the Greedy Bandit's estimate of `β_i` after time `t`. -/
noncomputable def est (i : Fin 2) (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  estOf β (fun s => X s ω) (fun j s => ε j s ω) (fun s => arm β X ε W s ω) i t

/-- The instantaneous expected regret
`r_t = E[max_j X_tᵀβ_j − X_tᵀβ_{π_t}]` at time `t`, expectation under `P`. -/
noncomputable def instRegret [MeasurableSpace Ω] (P : Measure Ω) (t : ℕ) : ℝ :=
  ∫ ω, (max (X t ω ⬝ᵥ β 0) (X t ω ⬝ᵥ β 1) - X t ω ⬝ᵥ β (arm β X ε W t ω)) ∂P

/-- The cumulative expected regret `R_T = ∑_{t=1}^T r_t`. -/
noncomputable def regret [MeasurableSpace Ω] (P : Measure Ω) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, instRegret β X ε W P t

end Run

/-! ## Constants -/

/-- `C̄ = 1/3 + (7/2)(log d)^{−1/2} + (38/3)(log d)^{−1} + (67/4)(log d)^{−3/2}`, display (4). -/
noncomputable def Cbar (d : ℕ) : ℝ :=
  1 / 3 + 7 / 2 * Real.log d ^ (-(1 / 2) : ℝ) + 38 / 3 * (Real.log d)⁻¹
    + 67 / 4 * Real.log d ^ (-(3 / 2) : ℝ)

/-- `C₁ = λ₀ / (40 x²_max)` (Lemma 4). -/
noncomputable def C1 (lam0 xmax : ℝ) : ℝ := lam0 / (40 * xmax ^ 2)

/-- `C₂ = λ² / (2 d σ² x²_max)` (Lemma 5). -/
noncomputable def C2 (lam : ℝ) (d : ℕ) (σ xmax : ℝ) : ℝ := lam ^ 2 / (2 * d * σ ^ 2 * xmax ^ 2)

/-- `C₃ = λ₀² / (32 d σ² x²_max)` (Lemma 6). -/
noncomputable def C3 (lam0 : ℝ) (d : ℕ) (σ xmax : ℝ) : ℝ :=
  lam0 ^ 2 / (32 * d * σ ^ 2 * xmax ^ 2)

end MostlyExplorationFree.GreedyBandit


