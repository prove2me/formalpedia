-- Prove2me | Definitions.Def_ExploreFirst_Asymptotic_Setting
-- name    : ExploreFirst_Asymptotic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:12.366184+00:00
-- url     : https://prove2.me/theorems/8adfb3d6-ab87-4333-8fcf-306d9beecde7
-- title:
--   Bandit model, optimal arms, and uniformly fast convergence (Definition 1)
-- statement:
--   A **bandit model** $\mathcal D$ is a collection of probability laws on $\mathbb R$ with finite expectation. A $K$-armed bandit $\underline\nu$ belongs to $\mathcal D$ when every arm's reward law belongs to it. The **optimal-arm set** $\mathcal A^\star(\underline\nu)$ consists of arms whose means attain the largest arm mean. For an arm $a$, write $N_{\psi,a}(T)$ for its number of draws through round $T$, and $\mathbb E_{\underline\nu}N_{\psi,a}(T)$ for its expected draw count.
--
--   Definition 1 calls a strategy $\psi$ **uniformly fast convergent** on $\mathcal D$ when, for every bandit problem $\underline\nu$ in $\mathcal D$, every arm $a$ with positive gap $\Delta_a$, and every $0<\alpha\le1$,
--
--   $$
--   \mathbb E_{\underline\nu}N_{\psi,a}(T)=o(T^\alpha)\qquad(T\to\infty).
--   $$
--
--   This condition controls every suboptimal arm on every problem in the model and is the strategy class of Theorem 1.
--
--   **Formalization Note** Arms are indexed from zero in Lean. Strategies are history-dependent Markov kernels. The little-o condition is convergence of the real ratio to zero along natural horizons. Expected draw counts use the bounded pull-count statistic from `ExploreFirst.FundIneq.Setting`, which this item imports.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, pp. 2–3, §1.1–1.2 (model and optimal arms); p. 9, Definition 1

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ConsistentBanditPolicy
import Definitions.Def_ExploreFirst_FundIneq_Setting

open MeasureTheory Filter ENNReal

namespace ExploreFirst.Asymptotic

/-- The paper's model consists of probability laws with finite first absolute moment. -/
def IsModel (𝒟 : Set (Measure ℝ)) : Prop :=
  ∀ P ∈ 𝒟, IsProbabilityMeasure P ∧ Integrable id P

/-- Every arm law of the bandit belongs to the model. -/
def InModel {K : ℕ} (𝒟 : Set (Measure ℝ))
    (ν : BanditAlgorithm.StochasticBandit K) : Prop :=
  ∀ a, ν.P a ∈ 𝒟

/-- The arms whose means attain the best mean. -/
noncomputable def optimalArms {K : ℕ} (ν : BanditAlgorithm.StochasticBandit K) : Finset (Fin K) :=
  Finset.univ.filter (fun a => BanditAlgorithm.banditArmMean ν a =
    BanditAlgorithm.banditOptimalMean ν)

/-- Definition 1: expected pulls of each suboptimal arm are `o(T^α)` for every `0 < α ≤ 1`,
uniformly over all bandit problems whose arms belong to the model. -/
def IsUniformlyFastConvergent {K : ℕ} (𝒟 : Set (Measure ℝ))
    (π : BanditAlgorithm.BanditPolicy K) : Prop :=
  ∀ ν : BanditAlgorithm.StochasticBandit K, InModel 𝒟 ν →
    ∀ a : Fin K, 0 < BanditAlgorithm.banditGap ν a →
      ∀ α : ℝ, 0 < α → α ≤ 1 →
        Tendsto (fun T : ℕ => ExploreFirst.FundIneq.expPulls ν π T a / (T : ℝ) ^ α) atTop (nhds 0)

end ExploreFirst.Asymptotic


