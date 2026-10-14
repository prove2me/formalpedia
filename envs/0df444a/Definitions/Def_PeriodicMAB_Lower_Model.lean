-- Prove2me | Definitions.Def_PeriodicMAB_Lower_Model
-- name    : PeriodicMAB_Lower_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:35.184806+00:00
-- url     : https://prove2.me/theorems/67282434-07a0-40b0-960c-b72c54a6c72e
-- title:
--   §2, §5, B.4, pp. 7, 12, 23, 46–49 — periodic Gaussian bandits: minimum period, history law, regret (1), classes ℰ₂(T₁), ℰ₃(T₁,…,T_K), metric (B-48), Assumption 3 with (7)
-- statement:
--   This file sets up the periodic multi-armed bandit with unit-variance Gaussian rewards used in the regret lower bounds of Chen, Wang and Wang.
--
--   **Arms, epochs and means.** There are $K$ arms, indexed $k = 0, \dots, K-1$ (the paper's arm $k+1$), and epochs $t = 1, 2, \dots$. An instance is a family of mean rewards $\mu_{k,t}$; only epochs $t \ge 1$ are meaningful. If arm $k$ is pulled at epoch $t$, the reward is drawn from $\mathcal N(\mu_{k,t}, 1)$.
--
--   **Minimum period.** A sequence $f$ has *minimum period* $p$ when $p \ge 1$, $f(t+p) = f(t)$ for every $t \ge 1$, and no $q$ with $1 \le q < p$ has the same property.
--
--   **History law.** A policy $\pi$ is a family of Markov kernels: at epoch $t$ it draws the arm $\pi_t$ from a distribution that depends on the past arms and rewards $(\pi_1, Y_1, \dots, \pi_{t-1}, Y_{t-1})$. The law of the history $(\pi_1, Y_1, \dots, \pi_T, Y_T)$ is built round by round: at epoch $t$ the arm is drawn from the policy's kernel and then the reward from $\mathcal N(\mu_{\pi_t, t}, 1)$. This is the joint density
--   $$q(a_1, y_1, \dots, a_T, y_T) = \prod_{t=1}^T \pi(a_t \mid a_1, y_1, \dots, a_{t-1}, y_{t-1})\, p(y_t - \mu_{a_t, t})$$
--   of p. 49, with $p$ the standard normal density.
--
--   **Regret (1).** The expected regret of $\pi$ over the horizon $T$ is
--   $$\mathbb E_\nu[R^\pi_T] = \sum_{t=1}^T \Big(\max_{k} \mu_{k,t} - \mathbb E[\mu_{\pi_t, t}]\Big).$$
--
--   **The classes.** Let $T$ be the horizon.
--   1. $\mathcal E_2(T_1)$: the first arm's mean $t \mapsto \mu_{1,t}$ has minimum period $T_1$, every other arm is stationary ($\mu_{k,t} = \mu_{k,1}$ for all $t \ge 1$), and all means lie in $[0,1]$ for $1 \le t \le T$ (Assumption 1).
--   2. $\mathcal E_3(T_1, \dots, T_K)$: arm $k$'s mean has minimum period $T_k$ for every $k$, and all means lie in $[0,1]$ for $1 \le t \le T$.
--
--   **Metric (B-48).** For two instances $\nu_1, \nu_2$,
--   $$\mathcal M(\nu_1, \nu_2) = \Big(\sum_{k=1}^K \sum_{p=1}^{T_k} \big(\mu^{(\nu_1)}_{k,p} - \mu^{(\nu_2)}_{k,p}\big)^2\Big)^{1/2}.$$
--
--   **Assumption 3 with (7).** With $n = \lfloor \sqrt{T/K} \rfloor$ and $g = \lceil \sqrt n \rceil$: $T > 4K$, $g \ge 2$, and $T_k < n/(2g)$ for every arm $k$. (The condition $g \ge \sqrt n$ holds by construction.)
--
--   These objects are shared by every lower-bound statement of §5 and Appendix B.4.
--
--   **Formalization Note** Arms are `Fin K` (0-based) and epochs are 1-based natural numbers; history coordinate $i$ is epoch $i+1$. The history law reuses the platform's `BanditAlgorithm.banditStepKernel` with the Gaussian bandit whose mean vector is $(\mu_{k,t})_k$ at the current epoch $t$, so with constant means it coincides with `BanditAlgorithm.banditMeasure` of `BanditAlgorithm.gaussianBandit`. The maximum over arms is `Finset.sup'` over the nonempty `Fin K` (`[NeZero K]`). Assumption 1 is stated on $1 \le t \le T$, as printed; values at $t = 0$ are ignored by every definition.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 7 (§2, Assumption 1, (1)), p. 12 (Assumption 3, (7)), p. 23 (ℰ₁, ℰ₂(T₁), ℰ₃), p. 46 (B.4), p. 48 ((B-48)), p. 49 (history density q)

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_PeriodicMAB_Upper_Model

namespace PeriodicMAB.Lower

open MeasureTheory ProbabilityTheory BanditAlgorithm

/-- The history law of a policy `π` on the unit-variance Gaussian bandit with time-varying means
`μ k t` (arm `k : Fin K`, epoch `t ≥ 1`): round `n + 1` (epoch `t = n + 1`) samples the arm
`A ~ π.select n (history)` and then the reward `Y ~ 𝒩(μ A (n + 1), 1)`, and appends `(A, Y)`.
History coordinate `i : Fin n` is epoch `i + 1`. This is the joint law `q(a₁, y₁, …, a_T, y_T)` of
p. 49; with constant means it is `BanditAlgorithm.banditMeasure` of a Gaussian bandit. -/
noncomputable def periodicMeasure {K : ℕ} (μ : Fin K → ℕ → ℝ) (π : BanditPolicy K) :
    (n : ℕ) → Measure (BanditHistory K n)
  | 0 => Measure.dirac (fun t ↦ t.elim0)
  | n + 1 =>
      ((periodicMeasure μ π n).compProd
          (banditStepKernel (gaussianBandit (fun a ↦ μ a (n + 1))) π n)).map
        (fun p ↦ Fin.snoc (α := fun _ ↦ Fin K × ℝ) p.1 p.2)

instance periodicMeasure.instIsProbabilityMeasure {K : ℕ} (μ : Fin K → ℕ → ℝ)
    (π : BanditPolicy K) (n : ℕ) : IsProbabilityMeasure (periodicMeasure μ π n) := by
  induction n with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
      rw [periodicMeasure]
      have := ih
      exact Measure.isProbabilityMeasure_map measurable_banditHistorySnoc.aemeasurable

/-- The expected regret (1) of `π` over the horizon `T` on the periodic Gaussian instance `μ`:
`E[R^π_T] = ∑_{t=1}^T (max_k µ_{k,t} − E[µ_{π_t,t}])`, with epoch `t = i + 1` for `i : Fin T`
and the arm `π_t` read from the history coordinate `i`. -/
noncomputable def periodicRegret {K : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (π : BanditPolicy K)
    (T : ℕ) : ℝ :=
  ∑ i : Fin T,
    (Finset.univ.sup' Finset.univ_nonempty (fun k ↦ μ k ((i : ℕ) + 1)) -
      ∫ h, μ (h i).1 ((i : ℕ) + 1) ∂(periodicMeasure μ π T))

/-- The class `ℰ₂(T₁)` (p. 23, p. 46): the first arm (index `0`) has minimum period `T₁`, every
other arm is stationary on the epochs `t ≥ 1`, and all means lie in `[0, 1]` for
`t ∈ {1, …, T}` (Assumption 1). Rewards are unit-variance Gaussian (`periodicMeasure`). -/
def InE2 {K : ℕ} [NeZero K] (T T₁ : ℕ) (μ : Fin K → ℕ → ℝ) : Prop :=
  PeriodicMAB.Upper.IsMinPeriod (μ 0) T₁ ∧ (∀ k, k ≠ 0 → ∀ t, 1 ≤ t → μ k t = μ k 1) ∧
    ∀ k t, 1 ≤ t → t ≤ T → μ k t ∈ Set.Icc (0 : ℝ) 1

/-- The class `ℰ₃(T₁, …, T_K)` (p. 23, p. 46): arm `k` has minimum period `Tper k`, and all means
lie in `[0, 1]` for `t ∈ {1, …, T}` (Assumption 1). -/
def InE3 {K : ℕ} (T : ℕ) (Tper : Fin K → ℕ) (μ : Fin K → ℕ → ℝ) : Prop :=
  (∀ k, PeriodicMAB.Upper.IsMinPeriod (μ k) (Tper k)) ∧ ∀ k t, 1 ≤ t → t ≤ T → μ k t ∈ Set.Icc (0 : ℝ) 1

/-- The metric (B-48): `ℳ(ν₁, ν₂) = (∑_k ∑_{p=1}^{T_k} (µ^{(ν₁)}_{k,p} − µ^{(ν₂)}_{k,p})²)^{1/2}`. -/
noncomputable def instDist {K : ℕ} (Tper : Fin K → ℕ) (μ₁ μ₂ : Fin K → ℕ → ℝ) : ℝ :=
  Real.sqrt (∑ k, ∑ p ∈ Finset.Icc 1 (Tper k), (μ₁ k p - μ₂ k p) ^ 2)

/-- The stage-one length `n = ⌊√(T/K)⌋` of (7). -/
noncomputable def stageOneLength (K T : ℕ) : ℕ := ⌊Real.sqrt ((T : ℝ) / K)⌋₊

/-- The parameter `g = ⌈√n⌉` of (7). -/
noncomputable def gParam (n : ℕ) : ℕ := ⌈Real.sqrt n⌉₊

/-- Assumption 3 (p. 12) with the parameters (7): `T > 4K`, `g ≥ max{2, √n}` and
`T_k < n / (2g)` for every arm, where `n = ⌊√(T/K)⌋` and `g = ⌈√n⌉`
(`g ≥ √n` holds by construction). -/
def Assumption3 (K T : ℕ) (Tper : Fin K → ℕ) : Prop :=
  4 * K < T ∧ 2 ≤ gParam (stageOneLength K T) ∧
    ∀ k, (Tper k : ℝ) < (stageOneLength K T : ℝ) / (2 * (gParam (stageOneLength K T) : ℝ))

end PeriodicMAB.Lower


