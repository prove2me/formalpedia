-- Prove2me | Definitions.Def_AdaDiscRL_regret
-- name    : AdaDiscRL_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:53.338981+00:00
-- url     : https://prove2.me/theorems/f4cc6022-8293-45e0-aeb5-cc930d486300
-- title:
--   Regret of AdaMB or AdaQL over $K$ episodes
-- statement:
--   The **regret** after $K$ episodes is
--   $$
--   \mathrm{Regret}(K)=\sum_{k=1}^K\Big(V^\star_1(X^k_1)-V^{\pi^k}_1(X^k_1)\Big),
--   $$
--   where $\pi^k$ is the policy the algorithm deploys in episode $k$: at step $h$ in state $x$ it selects $\arg\max_{B\in\mathrm{RELEVANT}_h(x)}\overline{\mathbf Q}^{k-1}_h(B)$ and plays the action law of that ball.
--
--   **Formalization Note** The regret is a function of the data sequence; on a run it is a random variable.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Definition 2.3, Eq. (4), p.9

import Mathlib
import Definitions.Def_AdaDiscRL_optValue
import Definitions.Def_AdaDiscRL_polValue
import Definitions.Def_AdaDiscRL_AlgState

open MeasureTheory ProbabilityTheory

namespace AdaDiscRL

variable {S A ι : Type*} [MeasurableSpace S] [MeasurableSpace A]
  {D : S × A → S × A → ℝ} {dS Lmax H : ℕ}

/-- The policy `π^k` the algorithm deploys in episode `k` (arXiv:2110.15843v3, p.9 and §3.2,
p.16): at step `h` in state `x`, select `B = argmax_{RELEVANT_h(x)} Q̄_h^{k−1}(B)` from the state
`σ = σ^{k−1}` and play `play B x`. -/
noncomputable def greedyPolicy (P : HierPartition S A ι D dS Lmax)
    (choose : Finset ι → (ι → ℝ) → ι) (play : ι → Kernel S A) (σ : AlgState S ι H) :
    Fin H → S → Measure A :=
  fun h x => play (selBall P choose σ h x) x

/-- **Regret** (arXiv:2110.15843v3, Definition 2.3, Eq. (4), p.9) of the algorithm `alg` on the
data sequence `data`:
`Regret(K) = Σ_{k=1}^K (V⋆_1(X_1^k) − V_1^{π^k}(X_1^k))`, with `π^k` the greedy policy of the state
after episode `k − 1`. -/
noncomputable def regret (M : EpisodicMDP S A H) (P : HierPartition S A ι D dS Lmax)
    (choose : Finset ι → (ι → ℝ) → ι) (play : ι → Kernel S A)
    (alg : (ℕ → EpData S A H) → ℕ → AlgState S ι H) (K : ℕ) (data : ℕ → EpData S A H) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K,
    (optVRem M H ((data k).1 0) -
      polVRem M (greedyPolicy P choose play (alg data (k - 1))) H ((data k).1 0))

end AdaDiscRL


