-- Prove2me | Definitions.Def_StochasticBandit
-- name    : StochasticBandit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-17T20:09:33.331871+00:00
-- url     : https://prove2.me/theorems/0ee47234-3591-409f-a9bc-10967234be29
-- statement:
--   A stochastic $k$-armed bandit environment: a tuple $\nu = (P_1, \dots, P_k)$ of reward distributions (probability measures on $\mathbb{R}$) with means $\mu_i$. The optimal mean and the suboptimality gaps are
--
--   $$\mu^* = \max_i \mu_i, \qquad \Delta_i = \mu^* - \mu_i.$$
--
--   Also includes the 1-subgaussian environment class $\mathcal{E}^k_{SG}(1)$ (each $P_i$ has mean $\mu_i$ and $P_i$-centered rewards are 1-subgaussian), the standing assumption of Chapters 6-9.
-- source:
--   L&S Ch 4.1-4.5 pp.56-63; class defined at top of Ch 6, p.91

import Mathlib.Probability.Moments.SubGaussian

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapter 4 (§4.1-§4.5)
and the standing 1-subgaussian assumption of Chapters 6-9 (top of Ch 6, p.91).

A stochastic `k`-armed bandit is a tuple of reward (probability) distributions
on `ℝ`, one per arm, with means `μ i`, optimal mean `μ* = max_i μ i` and
suboptimality gaps `Δ i = μ* - μ i`.
-/

open MeasureTheory ProbabilityTheory NNReal

namespace BanditAlgorithm

/-- A stochastic `k`-armed bandit environment (L&S §4.1): a probability
distribution of rewards for each arm. -/
structure StochasticBandit (k : ℕ) where
  /-- The reward distribution of each arm. -/
  P : Fin k → Measure ℝ
  /-- Each arm's reward distribution is a probability measure. -/
  prob : ∀ i, IsProbabilityMeasure (P i)

attribute [instance] StochasticBandit.prob

/-- The mean reward `μ i` of arm `i`. -/
noncomputable def banditArmMean {k : ℕ} (ν : StochasticBandit k) (i : Fin k) : ℝ :=
  ∫ x, x ∂(ν.P i)

/-- The optimal mean reward `μ* = max_i μ i` (L&S §4.4). -/
noncomputable def banditOptimalMean {k : ℕ} (ν : StochasticBandit k) : ℝ :=
  ⨆ i, banditArmMean ν i

/-- The suboptimality gap `Δ i = μ* - μ i` of arm `i` (L&S §4.5). -/
noncomputable def banditGap {k : ℕ} (ν : StochasticBandit k) (i : Fin k) : ℝ :=
  banditOptimalMean ν - banditArmMean ν i

/-- The environment class `𝓔^k_SG(σ)`: every arm has integrable rewards and
`σ`-subgaussian centered reward `X - μ i` (standing assumption of L&S Ch 6-9;
`σ`-subgaussian = Mathlib's `HasSubgaussianMGF` with variance proxy `σ^2`). -/
def IsSubgaussianBandit {k : ℕ} (σ : ℝ≥0) (ν : StochasticBandit k) : Prop :=
  (∀ i, Integrable id (ν.P i)) ∧
  (∀ i, HasSubgaussianMGF (fun x ↦ x - banditArmMean ν i) (σ ^ 2) (ν.P i))

end BanditAlgorithm


