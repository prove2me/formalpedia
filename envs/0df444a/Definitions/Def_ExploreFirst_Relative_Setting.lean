-- Prove2me | Definitions.Def_ExploreFirst_Relative_Setting
-- name    : ExploreFirst_Relative_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:03.302389+00:00
-- url     : https://prove2.me/theorems/94a25197-96cd-4467-adf4-2c76c29b2478
-- title:
--   Definition 3, p. 11 — pairwise symmetry for optimal arms; truncated counts N⁺, p. 12
-- statement:
--   A **bandit problem** $\underline\nu=(\nu_a)_{a=1}^K$ assigns a reward distribution to each arm. Write $\mu_a$ for the arm means, $\mu^\star$ for their maximum, and $\mathcal A^\star(\underline\nu)$ for the optimal arms. A **strategy** $\psi$ selects the next arm from the observed past, possibly at random. The model $\mathcal D$ is a set of probability laws with finite expectation.
--
--   Definition 3 calls $\psi$ **pairwise symmetric for optimal arms** on $\mathcal D$ when, for every bandit problem $\underline\nu$ whose arm laws lie in $\mathcal D$, every pair $b,c\in\mathcal A^\star(\underline\nu)$ with identical laws $\nu_b=\nu_c$, and every horizon $T\ge1$, the pairs
--
--   $$
--   \big(N_{\psi,b}(T),N_{\psi,c}(T)\big)\quad\text{and}\quad
--   \big(N_{\psi,c}(T),N_{\psi,b}(T)\big)
--   $$
--
--   have the same joint distribution. This only constrains pairs of optimal arms with identical reward laws. The item also defines the **truncated count** $N^+_{\psi,a}(T)=\max\{N_{\psi,a}(T),1\}$ as a real-valued statistic, as used in the proof of Theorem 3.
--
--   **Formalization Note** Arms are zero-indexed in Lean. The strategy is a history-dependent Markov kernel and the joint distributions are push-forwards of the bandit history measure under the count-pair maps. The model and optimal-arm definitions come from `ExploreFirst.Asymptotic.Setting`; they are imported here.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 11, §3.2, Definition 3; p. 12, proof of Theorem 3 (N⁺)

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ExploreFirst_Asymptotic_Setting
import Definitions.Def_ExploreFirst_FundIneq_Setting

namespace ExploreFirst.Relative

open MeasureTheory ProbabilityTheory BanditAlgorithm

/-- Definition 3, p. 11: a strategy is pairwise symmetric for optimal arms on `𝒟` if, for every
bandit problem in `𝒟` and every pair of optimal arms with the same distribution, the pair of
their pull counts and the swapped pair have the same joint law, for all `T ≥ 1`. -/
def IsPairwiseSymmetric {K : ℕ} (𝒟 : Set (Measure ℝ)) (π : BanditPolicy K) : Prop :=
  ∀ ν : StochasticBandit K, ExploreFirst.Asymptotic.InModel 𝒟 ν → ∀ b ∈ ExploreFirst.Asymptotic.optimalArms ν, ∀ c ∈ ExploreFirst.Asymptotic.optimalArms ν,
    ν.P b = ν.P c → ∀ T : ℕ, 1 ≤ T →
    (banditMeasure ν π T).map (fun h => (armPullCount b h, armPullCount c h)) =
    (banditMeasure ν π T).map (fun h => (armPullCount c h, armPullCount b h))

/-- `N⁺_{ψ,a}(T) = max{N_{ψ,a}(T), 1}` (p. 12), as a real number, on a history `h`. -/
noncomputable def pullsPlus {K T : ℕ} (a : Fin K) (h : BanditHistory K T) : ℝ :=
  max (armPullCount a h : ℝ) 1

end ExploreFirst.Relative


