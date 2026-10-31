-- Prove2me | Definitions.Def_FoundationsRL_EluderUCB_IsStructuredBanditProcess
-- name    : FoundationsRL_EluderUCB_IsStructuredBanditProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:41.038331+00:00
-- url     : https://prove2.me/theorems/6d1f2937-3a07-4ad5-9552-891434abb6ff
-- title:
--   The structured bandit protocol with stochastic rewards
-- statement:
--   A probability space with a filtration $(\mathcal H_t)$ carries a run of the structured bandit protocol with model $M^\star$ over $T$ rounds if, for each $t\in[T]$:
--
--   1. the decision $\pi^t\in\Pi$ and the reward $r^t\in\mathbb R$ are known after round $t$;
--   2. given the past and the decision, the reward has law $M^\star(\cdot\mid\pi^t)$:
--
--   $$
--   \mathbb P\bigl(r^t\in B\mid\mathcal H_{t-1},\pi^t\bigr)=M^\star(B\mid\pi^t)\quad\text{for every measurable } B\subseteq\mathbb R.
--   $$
--
--   The decision rule is arbitrary and may be randomized. This is the setting of Lemma 10 and of Proposition 12.
--
--   **Formalization Note** The filtration may carry more than the history, for example internal randomness of the algorithm; the natural filtration of the history is a special case.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Structured Bandit Protocol, p. 56, Assumption 4, (4.1), p. 57

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_preRewardSigma

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.EluderUCB

/-- **The structured bandit protocol with stochastic rewards.** Foster & Rakhlin,
arXiv:2312.16730v1, Structured Bandit Protocol, p. 56, and Assumption 4, (4.1), p. 57.

For rounds `t = 1, …, T`, a decision `πᵗ` is selected and a reward `rᵗ` is observed, and the
conditional law of `rᵗ` given the past and `πᵗ` is `M⋆(· | πᵗ)`. The algorithm is arbitrary and may
be randomized: `πᵗ` need only be known after round `t`, and the filtration `𝓗` may carry internal
randomness.

**Formalization Note.** Conditional law is written on measurable sets:
`P(rᵗ ∈ B | 𝓗_{t-1}, πᵗ) = M⋆(B | πᵗ)`. Indices `0` and `> T` of the processes are unused. -/
structure IsStructuredBanditProcess {Ω Act : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace Act]
    (P : Measure Ω) (𝓗 : Filtration ℕ mΩ) (M : Kernel Act ℝ) (T : ℕ)
    (π : ℕ → Ω → Act) (r : ℕ → Ω → ℝ) : Prop where
  /-- The decision of round `t` is known after round `t`. -/
  measurable_decision : ∀ t ∈ Finset.Icc 1 T, Measurable[𝓗 t] (π t)
  /-- The reward of round `t` is known after round `t`. -/
  measurable_reward : ∀ t ∈ Finset.Icc 1 T, Measurable[𝓗 t] (r t)
  /-- (4.1): given the past and `πᵗ`, the reward `rᵗ` has law `M⋆(· | πᵗ)`. -/
  reward_law : ∀ t ∈ Finset.Icc 1 T, ∀ B : Set ℝ, MeasurableSet B →
    P[(r t ⁻¹' B).indicator (fun _ => (1 : ℝ)) | preRewardSigma 𝓗 π t]
      =ᵐ[P] fun ω => (M (π t ω)).real B

end FoundationsRL.EluderUCB


