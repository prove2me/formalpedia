-- Prove2me | Definitions.Def_BwSC_LowerBound_Supplement_Environment
-- name    : BwSC_LowerBound_Supplement_Environment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:41:41.585535+00:00
-- url     : https://prove2.me/theorems/f730addd-2096-4878-9c98-9a5718a83990
-- title:
--   §1.2 and Definition 1 — normalized environments, admissible policies and worst-case regret
-- statement:
--   Let $K$ be the number of arms, $S$ the nonnegative integer switching budget and $T$ the horizon. An environment $\nu=(\nu_i)_{i\in[K]}$ is admissible if every reward is integrable, its centered moment generating function has variance proxy one, and its arm means $\mu_i$ have spread at most one. An admissible policy obeys
--   $$\mathbb P_{\nu,\pi}\!\left\{\sum_{t=1}^{T-1}\mathbf 1\{a_t\ne a_{t+1}\}\le S\right\}=1\quad\text{for every admissible }\nu.$$
--   The worst-case regret is $\sup_{\nu} R^\pi_\nu(K,T)$ over this environment class, where $R^\pi_\nu$ is the published canonical expected regret.
--
--   These definitions provide the common model for the supplement's upper bounds and its gap-weighted lower bound.
--
--   **Formalization Note** The existing bandit environment, policy, history law, regret and switching count are reused. This policy class is distinct from the base mission's Gaussian-only predicate. Histories use zero-based indices; switches compare consecutive actual rounds. The supremum has values in the extended reals, so unbounded sets cannot collapse to zero. Theorems 1 and 6 use equivalent uniform bounds for every environment.
-- source:
--   Simchi-Levi & Xu, arXiv:1905.10825v4, pp. 3–4, §1.2, Definition 1; p. 14, §3

import Mathlib
import Definitions.Def_BwSC_LowerBound_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound.Supplement

/-- The exact environment class of §1.2, p. 3: integrable, centered
1-sub-Gaussian rewards, and mean spread at most one. -/
def AdmissibleEnvironment {K : ℕ} (ν : StochasticBandit K) : Prop :=
  IsSubgaussianBandit 1 ν ∧
    ∀ i j, |banditArmMean ν i - banditArmMean ν j| ≤ 1

/-- Definition 1, p. 4, in the unit-cost model of §3, p. 14.
Unlike the base mission's Gaussian-only predicate, this quantifies over exactly
all admissible sub-Gaussian environments. -/
def IsAdmissiblePolicy {K : ℕ} (S T : ℕ) (π : BanditPolicy K) : Prop :=
  ∀ ν : StochasticBandit K, AdmissibleEnvironment ν →
    ∀ᵐ h ∂(banditMeasure ν π T), switchCost h 1 T ≤ S

/-- Worst-case regret, p. 4. Extended-real supremum avoids conditional
completeness defaults; the upper bounds below are stated instance by instance. -/
noncomputable def worstRegret {K : ℕ} (π : BanditPolicy K) (T : ℕ) : EReal :=
  ⨆ ν : {ν : StochasticBandit K // AdmissibleEnvironment ν},
    (banditRegret ν.val π T : EReal)

end BwSC.LowerBound.Supplement


